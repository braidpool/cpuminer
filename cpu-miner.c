/*
 * Copyright 2010 Jeff Garzik
 * Copyright 2012-2017 pooler
 *
 * This program is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by the Free
 * Software Foundation; either version 2 of the License, or (at your option)
 * any later version.  See COPYING for more details.
 */

#include "cpuminer-config.h"
#define _GNU_SOURCE

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <inttypes.h>
#include <unistd.h>
#include <sys/time.h>
#include <time.h>
#ifdef WIN32
#include <windows.h>
#else
#include <errno.h>
#include <signal.h>
#include <sys/resource.h>
#if HAVE_SYS_SYSCTL_H
#include <sys/types.h>
#if HAVE_SYS_PARAM_H
#include <sys/param.h>
#endif
#include <sys/sysctl.h>
#endif
#endif
#include <jansson.h>
#include <curl/curl.h>
#include "compat.h"
#include "miner.h"

#define PROGRAM_NAME        "minerd"
#define LP_SCANTIME        60

#ifdef __linux /* Linux specific policy and affinity management */
#include <sched.h>
static inline void drop_policy(void)
{
    struct sched_param param;
    param.sched_priority = 0;

#ifdef SCHED_IDLE
    if (unlikely(sched_setscheduler(0, SCHED_IDLE, &param) == -1))
#endif
#ifdef SCHED_BATCH
        sched_setscheduler(0, SCHED_BATCH, &param);
#endif
}

static inline void affine_to_cpu(int id, int cpu)
{
    cpu_set_t set;

    CPU_ZERO(&set);
    CPU_SET(cpu, &set);
    sched_setaffinity(0, sizeof(set), &set);
}
#elif defined(__FreeBSD__) /* FreeBSD specific policy and affinity management */
#include <sys/cpuset.h>
static inline void drop_policy(void)
{
}

static inline void affine_to_cpu(int id, int cpu)
{
    cpuset_t set;
    CPU_ZERO(&set);
    CPU_SET(cpu, &set);
    cpuset_setaffinity(CPU_LEVEL_WHICH, CPU_WHICH_TID, -1, sizeof(cpuset_t), &set);
}
#else
static inline void drop_policy(void)
{
}

static inline void affine_to_cpu(int id, int cpu)
{
}
#endif

enum workio_commands {
    WC_GET_WORK,
    WC_SUBMIT_WORK,
};

struct workio_cmd {
    enum workio_commands    cmd;
    struct thr_info        *thr;
    union {
        struct work        *work;
    } u;
};

enum algos {
    ALGO_SCRYPT,        /* scrypt(1024,1,1) */
    ALGO_SHA256D,        /* SHA-256d */
};

static const char *algo_names[] = {
    [ALGO_SCRYPT]        = "scrypt",
    [ALGO_SHA256D]        = "sha256d",
};

bool opt_debug = false;
bool opt_protocol = false;
static bool opt_benchmark = false;
bool opt_redirect = true;
bool want_longpoll = true;
bool have_longpoll = false;
bool have_gbt = true;
bool allow_getwork = true;
bool want_stratum = true;
bool have_stratum = false;
bool use_syslog = false;
static bool opt_background = false;
static bool opt_quiet = false;
static int opt_retries = -1;
static int opt_fail_pause = 30;
int opt_timeout = 0;
static int opt_stratum_idle_secs = 900;   /* disconnect idle threshold */
static int opt_stratum_ping_secs = 60;    /* send ping if idle this long */
static int opt_scantime = 5;
static enum algos opt_algo = ALGO_SHA256D;
static int opt_scrypt_n = 1024;
static int opt_n_threads;
static int num_processors;
static char *rpc_url;
static char *rpc_userpass;
static char *rpc_user, *rpc_pass;
static char *opt_version_mask = NULL;
static bool opt_suggest_difficulty = false;
static bool difficulty_suggested = false;
static double suggested_difficulty = 0.0;
bool opt_debug_sample_canonical = false;
bool opt_debug_lax_target = false;
bool opt_debug_merkle_both = false;

static int pk_script_size;
static unsigned char pk_script[42];
static char coinbase_sig[101] = "";
char *opt_cert;
char *opt_proxy;
long opt_proxy_type;
struct thr_info *thr_info;
static int work_thr_id;
int longpoll_thr_id = -1;
int stratum_thr_id = -1;
struct work_restart *work_restart = NULL;
static struct stratum_ctx stratum;

pthread_mutex_t applog_lock;
static pthread_mutex_t stats_lock;

static unsigned long accepted_count = 0L;
static unsigned long rejected_count = 0L;
static double *thr_hashrates;

typedef struct {
    pthread_barrier_t start_barrier;
    pthread_barrier_t finish_barrier;
    volatile bool benchmark_active;
    time_t benchmark_start_time;
} benchmark_sync_t;

static benchmark_sync_t benchmark_sync;

/* Map a linear counter into the scattered bit positions of a mask. */
static inline uint32_t scatter_bits(uint32_t val, uint32_t mask)
{
    uint32_t out = 0;
    uint32_t bit = 1;
    while (mask) {
        uint32_t lsb = mask & -mask; /* extract lowest set bit */
        if (val & bit)
            out |= lsb;
        mask ^= lsb;
        bit <<= 1;
    }
    return out;
}

/* --- Diagnostics: track per-thread best hash and periodic logging --- */
static uint32_t (*thr_best_header)[20];
static uint32_t *thr_best_top_hint; /* top 32 bits (big endian) as a quick comparator */
static unsigned char (*thr_best_digest_bytes)[32]; /* canonical CPUNet digest bytes */
static bool *thr_best_set;
static time_t g_last_best_log = 0;

/* Return true if a <= b as 256-bit integers in miner word order (hash[7] msw). */
/* use words_leq_256 from miner.h */

/* Build canonical CPUNet digest from a header (20 words, miner layout). */
static inline void cpunet_digest_from_header(const uint32_t *header20, uint32_t out_words[8])
{
    unsigned char preimage[87];
    for (int i = 0; i < 20; i++)
        le32enc(preimage + 4 * i, header20[i]);
    memcpy(preimage + 80, "cpunet", 6);
    preimage[86] = 0x00;
    unsigned char out_bytes[32];
    sha256d(out_bytes, preimage, sizeof(preimage));
    for (int i = 0; i < 8; i++)
        out_words[i] = swab32(be32dec(out_bytes + 4 * i));
}

static inline void cpunet_digest_bytes_from_header(const uint32_t *header20, unsigned char out_bytes[32])
{
    unsigned char preimage[87];
    for (int i = 0; i < 20; i++)
        le32enc(preimage + 4 * i, header20[i]);
    memcpy(preimage + 80, "cpunet", 6);
    preimage[86] = 0x00;
    sha256d(out_bytes, preimage, sizeof(preimage));
}

/* Decode Bitcoin varint from [*pp, end). Advances *pp on success. */
static bool read_varint_ptr(const unsigned char **pp, const unsigned char *end, uint64_t *val)
{
    const unsigned char *p = *pp;
    if (p >= end) return false;
    unsigned char fb = *p++;
    if (fb < 0xfd) {
        *val = fb;
        *pp = p; return true;
    }
    if (fb == 0xfd) {
        if (p + 2 > end) return false;
        *val = (uint64_t)p[0] | ((uint64_t)p[1] << 8);
        p += 2; *pp = p; return true;
    }
    if (fb == 0xfe) {
        if (p + 4 > end) return false;
        *val = le32dec(p);
        p += 4; *pp = p; return true;
    }
    /* fb == 0xff */
    if (p + 8 > end) return false;
    uint64_t lo = le32dec(p);
    uint64_t hi = le32dec(p + 4);
    *val = lo | (hi << 32);
    p += 8; *pp = p; return true;
}

/* Compute txid = sha256d(legacy-serialization) from possibly-segwit raw tx bytes. */
static bool compute_txid_nonwitness(const unsigned char *tx, size_t len, unsigned char out[32])
{
    const unsigned char *p = tx;
    const unsigned char *end = tx + len;
    if (len < 10) return false;
    const unsigned char *ver = p; p += 4;
    if (p > end) return false;
    bool segwit = false;
    if (p + 2 <= end && p[0] == 0x00 && p[1] == 0x01) {
        segwit = true;
        p += 2; /* skip marker+flag */
    }
    const unsigned char *vin_start = p;
    uint64_t vin_cnt = 0;
    if (!read_varint_ptr(&p, end, &vin_cnt)) return false;
    for (uint64_t ii = 0; ii < vin_cnt; ++ii) {
        if (p + 32 + 4 > end) return false;
        p += 32 + 4; /* prevout */
        uint64_t slen = 0;
        if (!read_varint_ptr(&p, end, &slen)) return false;
        if (p + slen + 4 > end) return false; /* script + sequence */
        p += slen + 4;
    }
    uint64_t vout_cnt = 0;
    if (!read_varint_ptr(&p, end, &vout_cnt)) return false;
    for (uint64_t oo = 0; oo < vout_cnt; ++oo) {
        if (p + 8 > end) return false; /* value */
        p += 8;
        uint64_t pklen = 0;
        if (!read_varint_ptr(&p, end, &pklen)) return false;
        if (p + pklen > end) return false;
        p += pklen;
    }
    const unsigned char *vout_end = p;
    if (end < tx + 4) return false;
    const unsigned char *locktime_le = end - 4;
    /* Build legacy bytes: version + vin..vout + locktime */
    size_t body_len = (size_t)(vout_end - vin_start);
    size_t out_len = 4 + body_len + 4;
    unsigned char *buf = (unsigned char *)alloca(out_len);
    memcpy(buf, ver, 4);
    memcpy(buf + 4, vin_start, body_len);
    memcpy(buf + 4 + body_len, locktime_le, 4);
    sha256d(out, buf, out_len);
    return true;
}

/* Debug aid: enumerate block-hash variants under different endianness interpretations.
 * For each combination over:
 *  - Version: LE/BE
 *  - Prevhash: word-order Normal/Reversed x per-word bytes LE/BE
 *  - Merkle:   word-order Normal/Reversed x per-word bytes LE/BE
 *  - NTime: LE/BE
 *  - NBits: LE/BE
 *  - Nonce: LE/BE
 * Compute sha256d over the 80-byte header + "cpunet\0" and print hash in RPC hex. */
static void debug_dump_all_endian_hashes(const uint32_t *hdr20)
{
    unsigned char pre[87];
    const char *ord_name[2] = {"N", "R"};
    const char *end_name[2] = {"LE", "BE"};

    /* Print header fields in big-endian hex (RPC-style)
       Reconstruct by serializing header fields to little-endian bytes first,
       then reversing the full 32 bytes for 256-bit hashes. */
    {
        unsigned char ver_be[4], ntime_be[4], nbits_be[4], nonce_be[4];
        unsigned char prev_be[32], merk_be[32];
        char ver_hex[9], ntime_hex[9], nbits_hex[9], nonce_hex[9];
        char prev_hex[65], merk_hex[65];
        /* Build header bytes and print BE per field (reverse each slice) */
        unsigned char header80[80];
        for (int wi = 0; wi < 20; wi++)
            le32enc(header80 + 4 * wi, hdr20[wi]);
        for (int bi = 0; bi < 4; bi++) ver_be[bi]   = header80[3 - bi];
        if (have_stratum && stratum.job.prevhash)
            for (int bi = 0; bi < 32; bi++) prev_be[bi] = stratum.job.prevhash[bi];
        else
            for (int bi = 0; bi < 32; bi++) prev_be[bi] = header80[4 + 31 - bi];
        for (int bi = 0; bi < 32; bi++) merk_be[bi] = header80[36 + 31 - bi];
        for (int bi = 0; bi < 4; bi++)  ntime_be[bi] = header80[68 + 3 - bi];
        for (int bi = 0; bi < 4; bi++)  nbits_be[bi] = header80[72 + 3 - bi];
        for (int bi = 0; bi < 4; bi++)  nonce_be[bi] = header80[76 + 3 - bi];

        bin2hex(ver_hex,   ver_be,   4);
        bin2hex(ntime_hex, ntime_be, 4);
        bin2hex(nbits_hex, nbits_be, 4);
        bin2hex(nonce_hex, nonce_be, 4);
        bin2hex(prev_hex,  prev_be,  32);
        bin2hex(merk_hex,  merk_be,  32);

        applog(LOG_INFO, "Header fields (BE hex):");
        applog(LOG_INFO, "  version=%s", ver_hex);
        applog(LOG_INFO, "  prevhash=%s", prev_hex);
        applog(LOG_INFO, "  merkle  =%s", merk_hex);
        applog(LOG_INFO, "  ntime=%s nbits=%s nonce=%s", ntime_hex, nbits_hex, nonce_hex);
    }

    for (int mask = 0; mask < 256; mask++) {
        int v_be    = (mask >> 0) & 1;
        int p_rev   = (mask >> 1) & 1;
        int p_be    = (mask >> 2) & 1;
        int m_rev   = (mask >> 3) & 1;
        int m_be    = (mask >> 4) & 1;
        int t_be    = (mask >> 5) & 1;
        int b_be    = (mask >> 6) & 1;
        int n_be    = (mask >> 7) & 1;

        unsigned char *w = pre;
        /* version */
        if (v_be) be32enc(w, hdr20[0]); else le32enc(w, hdr20[0]);
        w += 4;
        /* prevhash: words 1..8 */
        for (int i = 0; i < 8; i++) {
            int idx = p_rev ? (8 - 1 - i) : i;
            if (p_be) be32enc(w, hdr20[1 + idx]); else le32enc(w, hdr20[1 + idx]);
            w += 4;
        }
        /* merkle: words 9..16 */
        for (int i = 0; i < 8; i++) {
            int idx = m_rev ? (8 - 1 - i) : i;
            if (m_be) be32enc(w, hdr20[9 + idx]); else le32enc(w, hdr20[9 + idx]);
            w += 4;
        }
        /* ntime, nbits, nonce */
        if (t_be) be32enc(w, hdr20[17]); else le32enc(w, hdr20[17]);
        w += 4;
        if (b_be) be32enc(w, hdr20[18]); else le32enc(w, hdr20[18]);
        w += 4;
        if (n_be) be32enc(w, hdr20[19]); else le32enc(w, hdr20[19]);
        w += 4;

        /* Append CPUNet marker */
        memcpy(pre + 80, "cpunet", 6);
        pre[86] = 0x00;

        unsigned char dig[32], dig_rpc[32];
        char hex[65];
        sha256d(dig, pre, sizeof(pre));
        for (int i = 0; i < 32; i++) dig_rpc[i] = dig[31 - i];
        bin2hex(hex, dig_rpc, 32);
        applog(LOG_INFO, "%s  [V=%s P=%s+%s M=%s+%s T=%s B=%s N=%s]",
               hex,
               end_name[v_be],
               ord_name[p_rev], end_name[p_be],
               ord_name[m_rev], end_name[m_be],
               end_name[t_be], end_name[b_be], end_name[n_be]);
    }
}

void miner_report_candidate(int thr_id, const uint32_t *pdata, uint32_t nonce, uint32_t top_hint)
{
    if (!thr_best_header || thr_id < 0)
        return;
    /* Accept all top_hint values, including zero (very good) */

    uint32_t header_copy[20];
    memcpy(header_copy, pdata, 80);
    header_copy[19] = nonce;

    if (opt_debug_sample_canonical) {
        unsigned char cand_bytes[32];
        cpunet_digest_bytes_from_header(header_copy, cand_bytes);
        if (!thr_best_set[thr_id] || memcmp(cand_bytes, thr_best_digest_bytes[thr_id], 32) < 0) {
            memcpy(thr_best_header[thr_id], header_copy, 80);
            memcpy(thr_best_digest_bytes[thr_id], cand_bytes, 32);
            thr_best_top_hint[thr_id] = top_hint;
            thr_best_set[thr_id] = true;
        }
    } else {
        if (!thr_best_set[thr_id] || top_hint < thr_best_top_hint[thr_id]) {
            /* Compute and store digest bytes only when improving best top_hint */
            unsigned char cand_bytes[32];
            cpunet_digest_bytes_from_header(header_copy, cand_bytes);
            memcpy(thr_best_header[thr_id], header_copy, 80);
            memcpy(thr_best_digest_bytes[thr_id], cand_bytes, 32);
            thr_best_top_hint[thr_id] = top_hint;
            thr_best_set[thr_id] = true;
        }
    }
}

#ifdef HAVE_GETOPT_LONG
#include <getopt.h>
#else
struct option {
    const char *name;
    int has_arg;
    int *flag;
    int val;
};
#endif

static char const usage[] = "\nUsage: " PROGRAM_NAME " [OPTIONS]\nOptions:\n"
    "  -a, --algo=ALGO       specify the algorithm to use\n"
    "                          scrypt    scrypt(1024, 1, 1)\n"
    "                          scrypt:N  scrypt(N, 1, 1)\n"
    "                          sha256d   SHA-256d with CPUNet modification (default)\n"
    "  -o, --url=URL         URL of mining server\n"
    "  -O, --userpass=U:P    username:password pair for mining server\n"
    "  -u, --user=USERNAME   username for mining server\n"
    "  -p, --pass=PASSWORD   password for mining server\n"
    "      --cert=FILE       certificate for mining server using SSL\n"
    "  -x, --proxy=[PROTOCOL://]HOST[:PORT]  connect through a proxy\n"
    "  -t, --threads=N       number of miner threads (default: number of processors)\n"
    "  -r, --retries=N       number of times to retry if a network call fails\n"
    "                          (default: retry indefinitely)\n"
    "  -R, --retry-pause=N   time to pause between retries, in seconds (default: 30)\n"
    "  -T, --timeout=N       timeout for long polling, in seconds (default: none)\n"
    "  -s, --scantime=N      upper bound on time spent scanning current work when\n"
    "                          long polling is unavailable, in seconds (default: 5)\n"
    "      --coinbase-addr=ADDR  payout address for solo mining\n"
    "      --coinbase-sig=TEXT  data to insert in the coinbase when possible\n"
    "      --no-longpoll     disable long polling support\n"
    "      --no-getwork      disable getwork support\n"
    "      --no-gbt          disable getblocktemplate support\n"
    "      --no-stratum      disable X-Stratum support\n"
    "      --no-redirect     ignore requests to change the URL of the mining server\n"
    "  -q, --quiet           disable per-thread hashmeter output\n"
    "  -D, --debug           enable debug output\n"
    "  -P, --protocol-dump   verbose dump of protocol-level activities\n"
#ifdef HAVE_SYSLOG_H
    "  -S, --syslog          use system log for output messages\n"
#endif
#ifndef WIN32
    "  -B, --background      run the miner in the background\n"
#endif
    "      --benchmark       run in offline benchmark mode\n"
    "  -c, --config=FILE     load a JSON-format configuration file\n"
    "  -V, --version         display version information and exit\n"
    "      --version-mask=MASK hex mask for version rolling\n"
    "      --suggest-difficulty  automatically suggest difficulty to pool\n"
    "      --stratum-idle=N   idle seconds before reconnect (default: 900)\n"
    "      --stratum-ping=N   ping interval seconds when idle (default: 60)\n"
    "      --debug-sample-canonical  sample one canonical digest per batch for display\n"
    "      --debug-lax-target    override share target to easy value (test submissions)\n"
    "      --debug-merkle-both   log merkle roots using both concat orders per level\n"
    "  -h, --help            display this help text and exit\n";

static char const short_options[] =
#ifndef WIN32
    "B"
#endif
#ifdef HAVE_SYSLOG_H
    "S"
#endif
    "a:c:Dhp:Px:qr:R:s:t:T:o:u:O:V";

static struct option const options[] = {
    { "algo", 1, NULL, 'a' },
#ifndef WIN32
    { "background", 0, NULL, 'B' },
#endif
    { "benchmark", 0, NULL, 1005 },
    { "cert", 1, NULL, 1001 },
    { "coinbase-addr", 1, NULL, 1013 },
    { "coinbase-sig", 1, NULL, 1015 },
    { "config", 1, NULL, 'c' },
    { "debug", 0, NULL, 'D' },
    { "help", 0, NULL, 'h' },
    { "no-gbt", 0, NULL, 1011 },
    { "no-getwork", 0, NULL, 1010 },
    { "no-longpoll", 0, NULL, 1003 },
    { "no-redirect", 0, NULL, 1009 },
    { "no-stratum", 0, NULL, 1007 },
    { "pass", 1, NULL, 'p' },
    { "protocol-dump", 0, NULL, 'P' },
    { "proxy", 1, NULL, 'x' },
    { "quiet", 0, NULL, 'q' },
    { "retries", 1, NULL, 'r' },
    { "retry-pause", 1, NULL, 'R' },
    { "scantime", 1, NULL, 's' },
#ifdef HAVE_SYSLOG_H
    { "syslog", 0, NULL, 'S' },
#endif
    { "threads", 1, NULL, 't' },
    { "timeout", 1, NULL, 'T' },
    { "url", 1, NULL, 'o' },
    { "user", 1, NULL, 'u' },
    { "userpass", 1, NULL, 'O' },
    { "version", 0, NULL, 'V' },
    { "version-mask", 1, NULL, 1016 },
    { "suggest-difficulty", 0, NULL, 1017 },
    { "stratum-idle", 1, NULL, 1018 },
    { "stratum-ping", 1, NULL, 1019 },
    { "debug-sample-canonical", 0, NULL, 1020 },
    { "debug-lax-target", 0, NULL, 1021 },
    { "debug-merkle-both", 0, NULL, 1022 },
    { 0, 0, 0, 0 }
};

struct work {
    uint32_t data[32];
    uint32_t target[8];

    int height;
    char *txs;
    char *workid;

    char *job_id;
    size_t xnonce2_len;
    unsigned char *xnonce2;

    uint32_t version_mask;
    uint32_t version_solution;
};

static struct work g_work;
static time_t g_work_time;
static pthread_mutex_t g_work_lock;
static bool submit_old = false;
static char *lp_id;

static inline void work_free(struct work *w)
{
    free(w->txs);
    free(w->workid);
    free(w->job_id);
    free(w->xnonce2);
}

static inline void work_copy(struct work *dest, const struct work *src)
{
    memcpy(dest, src, sizeof(struct work));
    if (src->txs)
        dest->txs = strdup(src->txs);
    if (src->workid)
        dest->workid = strdup(src->workid);
    if (src->job_id)
        dest->job_id = strdup(src->job_id);
    if (src->xnonce2) {
        dest->xnonce2 = malloc(src->xnonce2_len);
        memcpy(dest->xnonce2, src->xnonce2, src->xnonce2_len);
    }
}

static bool jobj_binary(const json_t *obj, const char *key,
            void *buf, size_t buflen)
{
    const char *hexstr;
    json_t *tmp;

    tmp = json_object_get(obj, key);
    if (unlikely(!tmp)) {
        applog(LOG_ERR, "JSON key '%s' not found", key);
        return false;
    }
    hexstr = json_string_value(tmp);
    if (unlikely(!hexstr)) {
        applog(LOG_ERR, "JSON key '%s' is not a string", key);
        return false;
    }
    if (!hex2bin(buf, hexstr, buflen))
        return false;

    return true;
}

static bool work_decode(const json_t *val, struct work *work)
{
    int i;

    if (unlikely(!jobj_binary(val, "data", work->data, sizeof(work->data)))) {
        applog(LOG_ERR, "JSON invalid data");
        goto err_out;
    }
    if (unlikely(!jobj_binary(val, "target", work->target, sizeof(work->target)))) {
        applog(LOG_ERR, "JSON invalid target");
        goto err_out;
    }

    for (i = 0; i < ARRAY_SIZE(work->data); i++)
        work->data[i] = le32dec(work->data + i);
    for (i = 0; i < ARRAY_SIZE(work->target); i++)
        work->target[i] = le32dec(work->target + i);

    return true;

err_out:
    return false;
}

static bool gbt_work_decode(const json_t *val, struct work *work)
{
    int i, n;
    uint32_t version, curtime, bits;
    uint32_t prevhash[8];
    uint32_t target[8];
    int cbtx_size;
    unsigned char *cbtx = NULL;
    unsigned char *tx = NULL;
    int tx_count, tx_size;
    unsigned char txc_vi[9];
    unsigned char (*merkle_tree)[32] = NULL;
    bool coinbase_append = false;
    bool submit_coinbase = false;
    bool segwit = false;
    json_t *tmp, *txa;
    bool rc = false;

    tmp = json_object_get(val, "rules");
    if (tmp && json_is_array(tmp)) {
        n = json_array_size(tmp);
        for (i = 0; i < n; i++) {
            const char *s = json_string_value(json_array_get(tmp, i));
            if (!s)
                continue;
            if (!strcmp(s, "segwit") || !strcmp(s, "!segwit"))
                segwit = true;
        }
    }

    tmp = json_object_get(val, "mutable");
    if (tmp && json_is_array(tmp)) {
        n = json_array_size(tmp);
        for (i = 0; i < n; i++) {
            const char *s = json_string_value(json_array_get(tmp, i));
            if (!s)
                continue;
            if (!strcmp(s, "coinbase/append"))
                coinbase_append = true;
            else if (!strcmp(s, "submit/coinbase"))
                submit_coinbase = true;
        }
    }

    tmp = json_object_get(val, "height");
    if (!tmp || !json_is_integer(tmp)) {
        applog(LOG_ERR, "JSON invalid height");
        goto out;
    }
    work->height = json_integer_value(tmp);

    tmp = json_object_get(val, "version");
    if (!tmp || !json_is_integer(tmp)) {
        applog(LOG_ERR, "JSON invalid version");
        goto out;
    }
    version = json_integer_value(tmp);

    if (unlikely(!jobj_binary(val, "previousblockhash", prevhash, sizeof(prevhash)))) {
        applog(LOG_ERR, "JSON invalid previousblockhash");
        goto out;
    }

    tmp = json_object_get(val, "curtime");
    if (!tmp || !json_is_integer(tmp)) {
        applog(LOG_ERR, "JSON invalid curtime");
        goto out;
    }
    curtime = json_integer_value(tmp);

    if (unlikely(!jobj_binary(val, "bits", &bits, sizeof(bits)))) {
        applog(LOG_ERR, "JSON invalid bits");
        goto out;
    }

    /* find count and size of transactions */
    txa = json_object_get(val, "transactions");
    if (!txa || !json_is_array(txa)) {
        applog(LOG_ERR, "JSON invalid transactions");
        goto out;
    }
    tx_count = json_array_size(txa);
    tx_size = 0;
    for (i = 0; i < tx_count; i++) {
        const json_t *tx = json_array_get(txa, i);
        const char *tx_hex = json_string_value(json_object_get(tx, "data"));
        if (!tx_hex) {
            applog(LOG_ERR, "JSON invalid transactions");
            goto out;
        }
        tx_size += strlen(tx_hex) / 2;
    }

    /* build coinbase transaction */
    tmp = json_object_get(val, "coinbasetxn");
    if (tmp) {
        const char *cbtx_hex = json_string_value(json_object_get(tmp, "data"));
        cbtx_size = cbtx_hex ? strlen(cbtx_hex) / 2 : 0;
        cbtx = malloc(cbtx_size + 100);
        if (cbtx_size < 60 || !hex2bin(cbtx, cbtx_hex, cbtx_size)) {
            applog(LOG_ERR, "JSON invalid coinbasetxn");
            goto out;
        }
    } else {
        int64_t cbvalue;
        if (!pk_script_size) {
            if (allow_getwork) {
                applog(LOG_INFO, "No payout address provided, switching to getwork");
                have_gbt = false;
            } else
                applog(LOG_ERR, "No payout address provided");
            goto out;
        }
        tmp = json_object_get(val, "coinbasevalue");
        if (!tmp || !json_is_number(tmp)) {
            applog(LOG_ERR, "JSON invalid coinbasevalue");
            goto out;
        }
        cbvalue = json_is_integer(tmp) ? json_integer_value(tmp) : json_number_value(tmp);
        cbtx = malloc(256);
        le32enc((uint32_t *)cbtx, 1); /* version */
        cbtx[4] = 1; /* in-counter */
        memset(cbtx+5, 0x00, 32); /* prev txout hash */
        le32enc((uint32_t *)(cbtx+37), 0xffffffff); /* prev txout index */
        cbtx_size = 43;
        /* BIP 34: height in coinbase */
        if (work->height >= 1 && work->height <= 16) {
            /* Use OP_1-OP_16 to conform to Bitcoin's implementation. */
            cbtx[42] = work->height + 0x50;
            cbtx[cbtx_size++] = 0x00; /* OP_0; pads to 2 bytes */
        }
        else {
            for (n = work->height; n; n >>= 8) {
                cbtx[cbtx_size++] = n & 0xff;
                if (n < 0x100 && n >= 0x80)
                    cbtx[cbtx_size++] = 0;
            }
            cbtx[42] = cbtx_size - 43;
        }
        cbtx[41] = cbtx_size - 42; /* scriptsig length */
        le32enc((uint32_t *)(cbtx+cbtx_size), 0xffffffff); /* sequence */
        cbtx_size += 4;
        cbtx[cbtx_size++] = segwit ? 2 : 1; /* out-counter */
        le32enc((uint32_t *)(cbtx+cbtx_size), (uint32_t)cbvalue); /* value */
        le32enc((uint32_t *)(cbtx+cbtx_size+4), cbvalue >> 32);
        cbtx_size += 8;
        cbtx[cbtx_size++] = pk_script_size; /* txout-script length */
        memcpy(cbtx+cbtx_size, pk_script, pk_script_size);
        cbtx_size += pk_script_size;
        if (segwit) {
            unsigned char (*wtree)[32] = calloc(tx_count + 2, 32);
            memset(cbtx+cbtx_size, 0, 8); /* value */
            cbtx_size += 8;
            cbtx[cbtx_size++] = 38; /* txout-script length */
            cbtx[cbtx_size++] = 0x6a; /* txout-script */
            cbtx[cbtx_size++] = 0x24;
            cbtx[cbtx_size++] = 0xaa;
            cbtx[cbtx_size++] = 0x21;
            cbtx[cbtx_size++] = 0xa9;
            cbtx[cbtx_size++] = 0xed;
            for (i = 0; i < tx_count; i++) {
                const json_t *tx = json_array_get(txa, i);
                const json_t *hash = json_object_get(tx, "hash");
                if (!hash || !hex2bin(wtree[1+i], json_string_value(hash), 32)) {
                    applog(LOG_ERR, "JSON invalid transaction hash");
                    free(wtree);
                    goto out;
                }
                memrev(wtree[1+i], 32);
            }
            n = tx_count + 1;
            while (n > 1) {
                if (n % 2)
                    memcpy(wtree[n], wtree[n-1], 32);
                n = (n + 1) / 2;
                for (i = 0; i < n; i++)
                    sha256d(wtree[i], wtree[2*i], 64);
            }
            memset(wtree[1], 0, 32);  /* witness reserved value = 0 */
            sha256d(cbtx+cbtx_size, wtree[0], 64);
            cbtx_size += 32;
            free(wtree);
        }
        le32enc((uint32_t *)(cbtx+cbtx_size), 0); /* lock time */
        cbtx_size += 4;
        coinbase_append = true;
    }
    if (coinbase_append) {
        unsigned char xsig[100];
        int xsig_len = 0;
        if (*coinbase_sig) {
            n = strlen(coinbase_sig);
            if (cbtx[41] + xsig_len + n <= 100) {
                memcpy(xsig+xsig_len, coinbase_sig, n);
                xsig_len += n;
            } else {
                applog(LOG_WARNING, "Signature does not fit in coinbase, skipping");
            }
        }
        tmp = json_object_get(val, "coinbaseaux");
        if (tmp && json_is_object(tmp)) {
            void *iter = json_object_iter(tmp);
            while (iter) {
                unsigned char buf[100];
                const char *s = json_string_value(json_object_iter_value(iter));
                n = s ? strlen(s) / 2 : 0;
                if (!s || n > 100 || !hex2bin(buf, s, n)) {
                    applog(LOG_ERR, "JSON invalid coinbaseaux");
                    break;
                }
                if (cbtx[41] + xsig_len + n <= 100) {
                    memcpy(xsig+xsig_len, buf, n);
                    xsig_len += n;
                }
                iter = json_object_iter_next(tmp, iter);
            }
        }
        if (xsig_len) {
            unsigned char *ssig_end = cbtx + 42 + cbtx[41];
            int push_len = cbtx[41] + xsig_len < 76 ? 1 :
                           cbtx[41] + 2 + xsig_len > 100 ? 0 : 2;
            n = xsig_len + push_len;
            memmove(ssig_end + n, ssig_end, cbtx_size - 42 - cbtx[41]);
            cbtx[41] += n;
            if (push_len == 2)
                *(ssig_end++) = 0x4c; /* OP_PUSHDATA1 */
            if (push_len)
                *(ssig_end++) = xsig_len;
            memcpy(ssig_end, xsig, xsig_len);
            cbtx_size += n;
        }
    }

    n = varint_encode(txc_vi, 1 + tx_count);
    work->txs = malloc(2 * (n + cbtx_size + tx_size) + 1);
    bin2hex(work->txs, txc_vi, n);
    bin2hex(work->txs + 2*n, cbtx, cbtx_size);
    char *txs_end = work->txs + strlen(work->txs);

    /* generate merkle root */
    merkle_tree = malloc(32 * ((1 + tx_count + 1) & ~1));
    size_t tx_buf_size = 32 * 1024;
    tx = malloc(tx_buf_size);
    sha256d(merkle_tree[0], cbtx, cbtx_size);
    for (i = 0; i < tx_count; i++) {
        tmp = json_array_get(txa, i);
        const char *tx_hex = json_string_value(json_object_get(tmp, "data"));
        const size_t tx_hex_len = tx_hex ? strlen(tx_hex) : 0;
        const int tx_size = tx_hex_len / 2;
        if (segwit) {
            const char *txid = json_string_value(json_object_get(tmp, "txid"));
            if (!txid || !hex2bin(merkle_tree[1 + i], txid, 32)) {
                applog(LOG_ERR, "JSON invalid transaction txid");
                goto out;
            }
            memrev(merkle_tree[1 + i], 32);
        } else {
            if (tx_size > tx_buf_size) {
                free(tx);
                tx_buf_size = tx_size * 2;
                tx = malloc(tx_buf_size);
            }
            if (!tx_hex || !hex2bin(tx, tx_hex, tx_size)) {
                applog(LOG_ERR, "JSON invalid transactions");
                goto out;
            }
            sha256d(merkle_tree[1 + i], tx, tx_size);
        }
        if (!submit_coinbase) {
            strcpy(txs_end, tx_hex);
            txs_end += tx_hex_len;
        }
    }
    free(tx); tx = NULL;
    n = 1 + tx_count;
    while (n > 1) {
        if (n % 2) {
            memcpy(merkle_tree[n], merkle_tree[n-1], 32);
            ++n;
        }
        n /= 2;
        for (i = 0; i < n; i++)
            sha256d(merkle_tree[i], merkle_tree[2*i], 64);
    }

    /* assemble block header */
    work->data[0] = swab32(version);
    for (i = 0; i < 8; i++)
        work->data[8 - i] = swab32(be32dec(prevhash + i));
    for (i = 0; i < 8; i++)
        work->data[9 + i] = swab32(be32dec((uint32_t *)merkle_tree[0] + i));
    work->data[17] = swab32(curtime);
    work->data[18] = swab32(be32dec(&bits));

    if (unlikely(!jobj_binary(val, "target", target, sizeof(target)))) {
        applog(LOG_ERR, "JSON invalid target");
        goto out;
    }
    for (i = 0; i < ARRAY_SIZE(work->target); i++)
        work->target[7 - i] = be32dec(target + i);

    tmp = json_object_get(val, "workid");
    if (tmp) {
        if (!json_is_string(tmp)) {
            applog(LOG_ERR, "JSON invalid workid");
            goto out;
        }
        work->workid = strdup(json_string_value(tmp));
    }

    /* Long polling */
    tmp = json_object_get(val, "longpollid");
    if (want_longpoll && json_is_string(tmp)) {
        free(lp_id);
        lp_id = strdup(json_string_value(tmp));
        if (!have_longpoll) {
            char *lp_uri;
            tmp = json_object_get(val, "longpolluri");
            lp_uri = strdup(json_is_string(tmp) ? json_string_value(tmp) : rpc_url);
            have_longpoll = true;
            tq_push(thr_info[longpoll_thr_id].q, lp_uri);
        }
    }

    rc = true;

out:
    free(tx);
    free(cbtx);
    free(merkle_tree);
    return rc;
}

static void share_result(int result, const char *reason)
{
    char s[345];
    double hashrate;
    int i;

    hashrate = 0.;
    pthread_mutex_lock(&stats_lock);
    for (i = 0; i < opt_n_threads; i++)
        hashrate += thr_hashrates[i];
    result ? accepted_count++ : rejected_count++;

    // Update suggested_difficulty with the current total hashrate
    // Convert to KHash/s as suggested_difficulty is in KHash/s
    if (opt_suggest_difficulty) {
        suggested_difficulty = hashrate / 1000.0;
        applog(LOG_INFO, "DEBUG: share_result: opt_suggest_difficulty is true. hashrate=%.2f, suggested_difficulty=%.4f", hashrate, suggested_difficulty);
    }

    pthread_mutex_unlock(&stats_lock);

    sprintf(s, hashrate >= 1e6 ? "%.0f" : "%.2f", 1e-3 * hashrate);
    applog(LOG_INFO, "accepted: %lu/%lu (%.2f%%), %s khash/s %s",
           accepted_count,
           accepted_count + rejected_count,
           100. * accepted_count / (accepted_count + rejected_count),
           s,
           result ? "(yay!!!)" : "(booooo)");

    if (opt_debug && reason)
        applog(LOG_DEBUG, "DEBUG: reject reason: %s", reason);
}

static bool submit_upstream_work(CURL *curl, struct work *work)
{
    json_t *val, *res, *reason;
    char data_str[2 * sizeof(work->data) + 1];
    char s[345];
    int i;
    bool rc = false;

    /* Debug: compute and print CPUNet block hash from exact wire header bytes (matches server). */
    do {
        unsigned char header80[80];
        for (int hi = 0; hi < 20; hi++)
            le32enc(header80 + 4 * hi, work->data[hi]);
        unsigned char digest[32], digest_rpc[32];
        /* CPUNet PoW: sha256d(header || "cpunet\0") */
        unsigned char preimage[87];
        memcpy(preimage, header80, 80);
        memcpy(preimage + 80, "cpunet", 6);
        preimage[86] = 0x00;
        sha256d(digest, preimage, sizeof(preimage));
        for (int bi = 0; bi < 32; bi++) digest_rpc[bi] = digest[31 - bi];
        char hash_hex[65];
        bin2hex(hash_hex, digest_rpc, 32);
        uint32_t ntime_be = swab32(work->data[17]);
        uint32_t bits_be  = swab32(work->data[18]);
        uint32_t nonce_be = swab32(work->data[19]);
        applog(LOG_INFO, "submit: block_hash=%s nonce=%08x ntime=%08x bits=%08x",
               hash_hex, nonce_be, ntime_be, bits_be);
        if (opt_debug || opt_debug_lax_target) {
            applog(LOG_INFO, "Enumerating endianness variants (hash in RPC order):");
            uint32_t header_words[20];
            for (int hi = 0; hi < 20; hi++) header_words[hi] = work->data[hi];
            debug_dump_all_endian_hashes(header_words);
        }
    } while (0);

    /* pass if the previous hash is not the current previous hash */
    if (!submit_old && memcmp(work->data + 1, g_work.data + 1, 32)) {
        if (opt_debug)
            applog(LOG_DEBUG, "DEBUG: stale work detected, discarding");
        return true;
    }

    if (have_stratum) {
        uint32_t ntime, nonce;
        char ntimestr[9], noncestr[9], *xnonce2str, *req, version_hex[20] = "";

        if (opt_version_mask) {
            /* Stratum expects the full rolled version (big-endian hex), not just the mask delta */
            sprintf(version_hex, ", \"%08x\"", swab32(work->data[0] & work->version_mask));
        }
        le32enc(&ntime, work->data[17]);
        le32enc(&nonce, work->data[19]);
        bin2hex(ntimestr, (const unsigned char *)(&ntime), 4);
        bin2hex(noncestr, (const unsigned char *)(&nonce), 4);
        xnonce2str = abin2hex(work->xnonce2, work->xnonce2_len);
        req = malloc(256 + strlen(rpc_user) + strlen(work->job_id) + 2 * work->xnonce2_len);
        sprintf(req,
            "{\"method\": \"mining.submit\", \"params\": [\"%s\", \"%s\", \"%s\", \"%s\", \"%s\"%s], \"id\":4}",
            rpc_user, work->job_id, xnonce2str, ntimestr, noncestr, version_hex);
        free(xnonce2str);

        rc = stratum_send_line(&stratum, req);
        free(req);
        if (unlikely(!rc)) {
            applog(LOG_ERR, "submit_upstream_work stratum_send_line failed");
            goto out;
        }

        /* In lax-target debug mode, send exactly one mining.submit then exit. */
        if (opt_debug_lax_target) {
            applog(LOG_INFO, "--debug-lax-target: sent one mining.submit; exiting");
            exit(0);
        }
    } else if (work->txs) {
        char *req;

        for (i = 0; i < ARRAY_SIZE(work->data); i++)
            be32enc(work->data + i, work->data[i]);
        bin2hex(data_str, (unsigned char *)work->data, 80);
        if (work->workid) {
            char *params;
            val = json_object();
            json_object_set_new(val, "workid", json_string(work->workid));
            params = json_dumps(val, 0);
            json_decref(val);
            req = malloc(128 + 2*80 + strlen(work->txs) + strlen(params));
            sprintf(req,
                "{\"method\": \"submitblock\", \"params\": [\"%s%s\", %s], \"id\":1}\r\n",
                data_str, work->txs, params);
            free(params);
        } else {
            req = malloc(128 + 2*80 + strlen(work->txs));
            sprintf(req,
                "{\"method\": \"submitblock\", \"params\": [\"%s%s\"], \"id\":1}\r\n",
                data_str, work->txs);
        }
        val = json_rpc_call(curl, rpc_url, rpc_userpass, req, NULL, 0);
        free(req);
        if (unlikely(!val)) {
            applog(LOG_ERR, "submit_upstream_work json_rpc_call failed");
            goto out;
        }

        res = json_object_get(val, "result");
        if (json_is_object(res)) {
            char *res_str;
            bool sumres = false;
            void *iter = json_object_iter(res);
            while (iter) {
                if (json_is_null(json_object_iter_value(iter))) {
                    sumres = true;
                    break;
                }
                iter = json_object_iter_next(res, iter);
            }
            res_str = json_dumps(res, 0);
            share_result(sumres, res_str);
            free(res_str);
        } else
            share_result(json_is_null(res), json_string_value(res));

        json_decref(val);
    } else {
        /* build hex string */
        for (i = 0; i < ARRAY_SIZE(work->data); i++)
            le32enc(work->data + i, work->data[i]);
        bin2hex(data_str, (unsigned char *)work->data, sizeof(work->data));

        /* build JSON-RPC request */
        sprintf(s,
            "{\"method\": \"getwork\", \"params\": [ \"%s\" ], \"id\":1}\r\n",
            data_str);

        /* issue JSON-RPC request */
        val = json_rpc_call(curl, rpc_url, rpc_userpass, s, NULL, 0);
        if (unlikely(!val)) {
            applog(LOG_ERR, "submit_upstream_work json_rpc_call failed");
            goto out;
        }

        res = json_object_get(val, "result");
        reason = json_object_get(val, "reject-reason");
        share_result(json_is_true(res), reason ? json_string_value(reason) : NULL);

        json_decref(val);
    }

    rc = true;

out:
    return rc;
}

static const char *getwork_req =
    "{\"method\": \"getwork\", \"params\": [], \"id\":0}\r\n";

#define GBT_CAPABILITIES "[\"coinbasetxn\", \"coinbasevalue\", \"longpoll\", \"workid\"]"
#define GBT_RULES "[\"segwit\"]"

static const char *gbt_req =
    "{\"method\": \"getblocktemplate\", \"params\": [{\"capabilities\": "
    GBT_CAPABILITIES ", \"rules\": " GBT_RULES "}], \"id\":0}\r\n";
static const char *gbt_lp_req =
    "{\"method\": \"getblocktemplate\", \"params\": [{\"capabilities\": "
    GBT_CAPABILITIES ", \"rules\": " GBT_RULES ", \"longpollid\": \"%s\"}], \"id\":0}\r\n";

static bool get_upstream_work(CURL *curl, struct work *work)
{
    json_t *val;
    int err;
    bool rc;
    struct timeval tv_start, tv_end, diff;

start:
    gettimeofday(&tv_start, NULL);
    val = json_rpc_call(curl, rpc_url, rpc_userpass,
                have_gbt ? gbt_req : getwork_req,
                &err, have_gbt ? JSON_RPC_QUIET_404 : 0);
    gettimeofday(&tv_end, NULL);

    if (have_stratum) {
        if (val)
            json_decref(val);
        return true;
    }

    if (!have_gbt && !allow_getwork) {
        applog(LOG_ERR, "No usable protocol");
        if (val)
            json_decref(val);
        return false;
    }

    if (have_gbt && allow_getwork && !val && err == CURLE_OK) {
        applog(LOG_INFO, "getblocktemplate failed, falling back to getwork");
        have_gbt = false;
        goto start;
    }

    if (!val)
        return false;

    if (have_gbt) {
        rc = gbt_work_decode(json_object_get(val, "result"), work);
        if (!have_gbt) {
            json_decref(val);
            goto start;
        }
    } else
        rc = work_decode(json_object_get(val, "result"), work);

    if (opt_debug && rc) {
        timeval_subtract(&diff, &tv_end, &tv_start);
        applog(LOG_DEBUG, "DEBUG: got new work in %d ms",
               diff.tv_sec * 1000 + diff.tv_usec / 1000);
    }

    json_decref(val);

    return rc;
}

static void workio_cmd_free(struct workio_cmd *wc)
{
    if (!wc)
        return;

    switch (wc->cmd) {
    case WC_SUBMIT_WORK:
        work_free(wc->u.work);
        free(wc->u.work);
        break;
    default: /* do nothing */
        break;
    }

    memset(wc, 0, sizeof(*wc));    /* poison */
    free(wc);
}

static bool workio_get_work(struct workio_cmd *wc, CURL *curl)
{
    struct work *ret_work;
    int failures = 0;

    ret_work = calloc(1, sizeof(*ret_work));
    if (!ret_work)
        return false;

    /* obtain new work from bitcoin via JSON-RPC */
    while (!get_upstream_work(curl, ret_work)) {
        if (unlikely((opt_retries >= 0) && (++failures > opt_retries))) {
            applog(LOG_ERR, "json_rpc_call failed, terminating workio thread");
            free(ret_work);
            return false;
        }

        /* pause, then restart work-request loop */
        applog(LOG_ERR, "json_rpc_call failed, retry after %d seconds",
            opt_fail_pause);
        sleep(opt_fail_pause);
    }

    /* send work to requesting thread */
    if (!tq_push(wc->thr->q, ret_work))
        free(ret_work);

    return true;
}

static bool workio_submit_work(struct workio_cmd *wc, CURL *curl)
{
    int failures = 0;

    /* submit solution to bitcoin via JSON-RPC */
    while (!submit_upstream_work(curl, wc->u.work)) {
        if (unlikely((opt_retries >= 0) && (++failures > opt_retries))) {
            applog(LOG_ERR, "...terminating workio thread");
            return false;
        }

        /* pause, then restart work-request loop */
        applog(LOG_ERR, "...retry after %d seconds",
            opt_fail_pause);
        sleep(opt_fail_pause);
    }

    return true;
}

static void *workio_thread(void *userdata)
{
    struct thr_info *mythr = userdata;
    CURL *curl;
    bool ok = true;

    curl = curl_easy_init();
    if (unlikely(!curl)) {
        applog(LOG_ERR, "CURL initialization failed");
        return NULL;
    }

    while (ok) {
        struct workio_cmd *wc;

        /* wait for workio_cmd sent to us, on our queue */
        wc = tq_pop(mythr->q, NULL);
        if (!wc) {
            ok = false;
            break;
        }

        /* process workio_cmd */
        switch (wc->cmd) {
        case WC_GET_WORK:
            ok = workio_get_work(wc, curl);
            break;
        case WC_SUBMIT_WORK:
            ok = workio_submit_work(wc, curl);
            break;

        default:        /* should never happen */
            ok = false;
            break;
        }

        workio_cmd_free(wc);
    }

    tq_freeze(mythr->q);
    curl_easy_cleanup(curl);

    return NULL;
}

static bool get_work(struct thr_info *thr, struct work *work)
{
    struct workio_cmd *wc;
    struct work *work_heap;

    if (opt_benchmark) {
        memset(work->data, 0x55, 76);
        work->data[17] = swab32(time(NULL));
        memset(work->target, 0x00, sizeof(work->target));
        return true;
    }

    /* fill out work request message */
    wc = calloc(1, sizeof(*wc));
    if (!wc)
        return false;

    wc->cmd = WC_GET_WORK;
    wc->thr = thr;

    /* send work request to workio thread */
    if (!tq_push(thr_info[work_thr_id].q, wc)) {
        workio_cmd_free(wc);
        return false;
    }

    /* wait for response, a unit of work */
    work_heap = tq_pop(thr->q, NULL);
    if (!work_heap)
        return false;

    /* copy returned work into storage provided by caller */
    memcpy(work, work_heap, sizeof(*work));
    free(work_heap);

    return true;
}

static bool submit_work(struct thr_info *thr, const struct work *work_in)
{
    struct workio_cmd *wc;

    /* fill out work request message */
    wc = calloc(1, sizeof(*wc));
    if (!wc)
        return false;

    wc->u.work = malloc(sizeof(*work_in));
    if (!wc->u.work)
        goto err_out;

    wc->cmd = WC_SUBMIT_WORK;
    wc->thr = thr;
    work_copy(wc->u.work, work_in);

    /* send solution to workio thread */
    if (!tq_push(thr_info[work_thr_id].q, wc))
        goto err_out;

    return true;

err_out:
    workio_cmd_free(wc);
    return false;
}

static void stratum_gen_work(struct stratum_ctx *sctx, struct work *work)
{
    unsigned char merkle_root[64];
    int i;

    pthread_mutex_lock(&sctx->work_lock);

    free(work->job_id);
    work->job_id = strdup(sctx->job.job_id);
    work->xnonce2_len = sctx->xnonce2_size;
    work->xnonce2 = realloc(work->xnonce2, sctx->xnonce2_size);
    memcpy(work->xnonce2, sctx->job.xnonce2, sctx->xnonce2_size);

    /* Generate merkle root (coinbase txid as leaf) */
    if (!compute_txid_nonwitness(sctx->job.coinbase, sctx->job.coinbase_size, merkle_root)) {
        /* Fallback: hash full coinbase bytes */
        sha256d(merkle_root, sctx->job.coinbase, sctx->job.coinbase_size);
    }
    for (i = 0; i < sctx->job.merkle_count; i++) {
        memcpy(merkle_root + 32, sctx->job.merkle[i], 32);
        sha256d(merkle_root, merkle_root, 64);
    }

    /* Optional: compute alternative merkle root using reversed concat order per level */
    if (opt_debug_merkle_both) {
        unsigned char cur[32], alt[32];
        unsigned char buf[64];
        /* Dump coinbase and extranonce layout */
        {
            char *cb_hex = abin2hex(sctx->job.coinbase, sctx->job.coinbase_size);
            char *x1_hex = abin2hex(sctx->xnonce1, sctx->xnonce1_size);
            char *x2_hex = abin2hex(sctx->job.xnonce2, sctx->xnonce2_size);
            applog(LOG_INFO, "coinbase(size=%zu): %s", sctx->job.coinbase_size, cb_hex);
            applog(LOG_INFO, "extranonce1(%zu): %s", sctx->xnonce1_size, x1_hex);
            applog(LOG_INFO, "extranonce2(%zu): %s", sctx->xnonce2_size, x2_hex);
            free(cb_hex); free(x1_hex); free(x2_hex);
            applog(LOG_INFO, "merkle_branches: %d", sctx->job.merkle_count);
        }
        memcpy(cur, merkle_root, 32); /* current root from normal path */
        /* Recompute both variants starting from coinbase txid to be precise */
        if (!compute_txid_nonwitness(sctx->job.coinbase, sctx->job.coinbase_size, cur))
            sha256d(cur, sctx->job.coinbase, sctx->job.coinbase_size);
        memcpy(alt, cur, 32);
        for (i = 0; i < sctx->job.merkle_count; i++) {
            /* Normal: cur || branch */
            memcpy(buf, cur, 32);
            memcpy(buf + 32, sctx->job.merkle[i], 32);
            sha256d(cur, buf, 64);
            /* Alternative: branch || cur */
            memcpy(buf, sctx->job.merkle[i], 32);
            memcpy(buf + 32, alt, 32);
            sha256d(alt, buf, 64);
        }
        /* Print both roots in RPC big-endian hex */
        unsigned char cur_be[32], alt_be[32];
        char cur_hex[65], alt_hex[65];
        for (int bi = 0; bi < 32; bi++) { cur_be[bi] = cur[31 - bi]; alt_be[bi] = alt[31 - bi]; }
        bin2hex(cur_hex, cur_be, 32);
        bin2hex(alt_hex, alt_be, 32);
        applog(LOG_INFO, "coinbase_txid (BE): %s", cur_hex);
        applog(LOG_INFO, "merkle(normal cur||branch): %s", cur_hex);
        applog(LOG_INFO, "merkle(alt branch||cur):   %s", alt_hex);
        /* Note: header still uses the normal variant above */
    }

    /* Increment extranonce2 */
    for (i = 0; i < sctx->xnonce2_size && !++sctx->job.xnonce2[i]; i++);

    /* Assemble block header */
    memset(work->data, 0, 128);
    /* version/ntime/nbits come from Stratum as big-endian hex; decode as BE */
    work->data[0] = swab32(be32dec(sctx->job.version));
    /* Stratum prevhash param is 32-byte BE hex. Header stores prevhash in LE bytes,
       i.e., reverse the full 32 bytes. Achieve this by reversing 32-bit word order
       and endian-swapping each word during serialization via le32enc later. */
    for (i = 0; i < 8; i++)
        work->data[1 + i] = swab32(be32dec((uint32_t *)sctx->job.prevhash + (7 - i)));
    for (i = 0; i < 8; i++)
        work->data[9 + i] = swab32(be32dec((uint32_t *)merkle_root + i));
    work->data[17] = swab32(be32dec(sctx->job.ntime));
    work->data[18] = swab32(be32dec(sctx->job.nbits));

    work->version_mask = sctx->job.version_mask;
    pthread_mutex_unlock(&sctx->work_lock);

    if (opt_debug) {
        char *xnonce2str = abin2hex(work->xnonce2, work->xnonce2_len);
        uint32_t ntime = swab32(work->data[17]);
        uint32_t nbits_le = work->data[18];
        applog(LOG_DEBUG, "JOB: id=%s clean=%d ntime=%08x nbits(le)=%08x vmask=%08x",
               work->job_id ? work->job_id : "(null)", sctx->job.clean, ntime, nbits_le, work->version_mask);
        free(xnonce2str);
    }

    if (opt_algo == ALGO_SCRYPT) {
        /* scrypt path kept as-is using legacy diff */
        diff_to_target(work->target, sctx->job.diff / 65536.0);
    } else {
        if (sctx->job.compact_bits) {
            compact_to_target_words(sctx->job.compact_bits, work->target);
        } else {
            diff_to_target(work->target, sctx->job.diff);
        }
    }
}



static void run_startup_benchmark(void)
{
    applog(LOG_INFO, "Running benchmark with %d threads...", opt_n_threads);

    benchmark_sync.benchmark_active = true;

    // Signal all threads to start benchmark
    pthread_barrier_wait(&benchmark_sync.start_barrier);

    // Wait for all threads to finish benchmark
    pthread_barrier_wait(&benchmark_sync.finish_barrier);

    benchmark_sync.benchmark_active = false;

    // Calculate total hashrate
    double total_hashrate = 0.0;
    for (int i = 0; i < opt_n_threads; i++) {
        total_hashrate += thr_hashrates[i];
    }

    // Store for difficulty suggestion
    suggested_difficulty = total_hashrate / 1000.0; // Convert to KHash/s

    char s[345];
    sprintf(s, total_hashrate >= 1e6 ? "%.0f" : "%.2f", 1e-3 * total_hashrate);
    applog(LOG_INFO, "Benchmark complete: %s khash/s", s);
}


static void *miner_thread(void *userdata)
{
    struct thr_info *mythr = userdata;
    int thr_id = mythr->id;
    struct work work = {{0}};
    uint32_t max_nonce;
    uint32_t start_nonce = 0xffffffffU / opt_n_threads * thr_id;
    uint32_t end_nonce = 0xffffffffU / opt_n_threads * (thr_id + 1) - 0x20;
    unsigned char *scratchbuf = NULL;
    char s[16];
    int i;
    /* Combined field state: lower 32b = nonce within thread slice, upper = version counter */
    uint32_t cur_nonce = start_nonce;
    uint32_t version_ctr = 0; /* advances when nonce wraps thread slice */

    /* Set worker threads to nice 19 and then preferentially to SCHED_IDLE
     * and if that fails, then SCHED_BATCH. No need for this to be an
     * error if it fails */
    if (!opt_benchmark) {
        setpriority(PRIO_PROCESS, 0, 19);
        drop_policy();
    }

    /*Cpu affinity only makes sense if the number of threads is a multiple
     * of the number of CPUs */
    if (num_processors > 1 && opt_n_threads % num_processors == 0) {
        if (opt_debug)
            applog(LOG_INFO, "Binding thread %d to cpu %d",
                   thr_id, thr_id % num_processors);
        affine_to_cpu(thr_id, thr_id % num_processors);
    }

    if (opt_algo == ALGO_SCRYPT) {
        scratchbuf = scrypt_buffer_alloc(opt_scrypt_n);
        if (!scratchbuf) {
            applog(LOG_ERR, "scrypt buffer allocation failed");
            pthread_mutex_lock(&applog_lock);
            exit(1);
        }
    }

    // Benchmark phase - all threads participate
    pthread_barrier_wait(&benchmark_sync.start_barrier);

    if (benchmark_sync.benchmark_active) {
        if (opt_debug) {
            applog(LOG_DEBUG, "thread %d starting benchmark", thr_id);
        }
        // Setup benchmark work
        memset(work.data, 0x55, 76);
        work.data[17] = swab32(time(NULL));
        memset(work.data + 19, 0x00, 52);
        work.data[20] = 0x80000000;
        work.data[31] = 0x00000280;
        memset(work.target, 0x00, sizeof(work.target));
        work.target[7] = 0x0000ffff; // Reasonable benchmark target
        work.data[19] = 0xffffffffU / opt_n_threads * thr_id;

        unsigned long hashes_done = 0;
        struct timeval tv_start, tv_end, diff;
        gettimeofday(&tv_start, NULL);

        // Run benchmark for a fixed duration
        const double benchmark_duration_ms = 1000.0;
        while (1) {
            uint32_t nonce_start = work.data[19];
            uint32_t max_nonce = nonce_start + 0x10000; // Small chunk
            unsigned long chunk_hashes = 0;

            int rc = 0;
            switch (opt_algo) {
            case ALGO_SCRYPT:
                rc = scanhash_scrypt(thr_id, work.data, scratchbuf, work.target,
                                    max_nonce, &chunk_hashes, opt_scrypt_n);
                break;
            case ALGO_SHA256D:
                rc = scanhash_sha256d(thr_id, work.data, work.target,
                                    max_nonce, &chunk_hashes);
                break;
            }
            hashes_done += chunk_hashes;
            work.data[19] = max_nonce;

            struct timeval tv_now, tv_start_copy;
            gettimeofday(&tv_now, NULL);
            tv_start_copy = tv_start;
            timeval_subtract(&diff, &tv_now, &tv_start_copy);
            double elapsed_ms = diff.tv_sec * 1000.0 + diff.tv_usec / 1000.0;
            if (opt_debug) {
                applog(LOG_DEBUG, "thr %d: benchmark loop, %lu hashes, %.2fms elapsed", thr_id, hashes_done, elapsed_ms);
            }
            if (elapsed_ms >= benchmark_duration_ms)
                break;
        }

        // Calculate hashrate for this thread
        gettimeofday(&tv_end, NULL);
        timeval_subtract(&diff, &tv_end, &tv_start);
        if (diff.tv_usec || diff.tv_sec) {
            thr_hashrates[thr_id] = hashes_done / (diff.tv_sec + 1e-6 * diff.tv_usec);
        }

        if (opt_debug) {
            sprintf(s, thr_hashrates[thr_id] >= 1e6 ? "%.0f" : "%.2f", 1e-3 * thr_hashrates[thr_id]);
            applog(LOG_DEBUG, "thread %d benchmark: %s khash/s (%lu hashes)", thr_id, s, hashes_done);
        }
    } else if (opt_debug) {
        applog(LOG_DEBUG, "thread %d skipped benchmark (not active)", thr_id);
    }

    if (opt_debug) {
        applog(LOG_DEBUG, "thread %d waiting at finish barrier", thr_id);
    }
    pthread_barrier_wait(&benchmark_sync.finish_barrier);

    if (opt_debug) {
        applog(LOG_DEBUG, "thread %d passed finish barrier", thr_id);
    }

    if (opt_benchmark)
        return NULL;

    

    // Regular mining loop
    while (1) {
        unsigned long total_hashes_done;
        struct timeval tv_start, tv_end, diff;
        int64_t max64;
        int rc = 0;

        if (have_stratum) {
            /* In Stratum mode, wait for a job and then take a snapshot to scan. */
            pthread_mutex_lock(&g_work_lock);
            if (!g_work.job_id) {
                pthread_mutex_unlock(&g_work_lock);
                usleep(100000); /* 100ms wait for first job */
                continue;
            }
            if (memcmp(work.data, g_work.data, 76) || work.data[19] >= end_nonce) {
                work_free(&work);
                work_copy(&work, &g_work);
                /* Reset nonce position to this thread's slice start on new job */
                cur_nonce = start_nonce;
                work.data[19] = cur_nonce;
                if (opt_debug) {
                    applog(LOG_DEBUG, "THREAD %d: new stratum work job=%s start_nonce=%08x target_top=%08x",
                           thr_id,
                           work.job_id ? work.job_id : "(null)",
                           work.data[19], work.target[7]);
                }
            } else {
                // Continue from current combined position
                work.data[19] = cur_nonce;
            }
            pthread_mutex_unlock(&g_work_lock);
        } else {
            int min_scantime = have_longpoll ? LP_SCANTIME : opt_scantime;
            /* obtain new work from internal workio thread */
            pthread_mutex_lock(&g_work_lock);
            if (!have_stratum &&
                (time(NULL) - g_work_time >= min_scantime ||
                 work.data[19] >= end_nonce)) {
                work_free(&g_work);
                if (!opt_benchmark && unlikely(!get_work(mythr, &g_work))) {
                    applog(LOG_ERR, "work retrieval failed, exiting "
                        "mining thread %d", mythr->id);
                    pthread_mutex_unlock(&g_work_lock);
                    goto out;
                }
                g_work_time = have_stratum ? 0 : time(NULL);
            }
        }

        /* At this point, 'work' holds a copy to scan. */
        if (work_restart[thr_id].restart && opt_debug) {
            applog(LOG_DEBUG, "THREAD %d: Clearing restart flag to begin work", thr_id);
        }
        work_restart[thr_id].restart = 0;

        /* Calculate nonce chunk size for ~100ms of work */
        double target_time_sec = 0.1; // 100ms target
        max64 = (int64_t)(thr_hashrates[thr_id] * target_time_sec);

        // Minimum chunk size to avoid too frequent reporting
        int64_t min_chunk = 0x10000; // 64k nonces minimum
        if (max64 < min_chunk) {
            max64 = min_chunk;
        }

        // Maximum chunk size to avoid too large ranges
        int64_t max_chunk = 0x1000000; // 16M nonces maximum
        if (max64 > max_chunk) {
            max64 = max_chunk;
        }

        // Ensure we don't go past our thread's assigned end_nonce within this chunk
        work.data[19] = cur_nonce;
        if (work.data[19] + max64 > end_nonce)
            max_nonce = end_nonce;
        else
            max_nonce = work.data[19] + max64;

        /* total_hashes_done is initialized below before scanning. */
        gettimeofday(&tv_start, NULL);
        struct timeval work_start_time = tv_start;  // Track when this work chunk started
        if (opt_debug) {
            double estimated_time_ms = thr_hashrates[thr_id] > 0 ?
                (max_nonce - work.data[19]) / thr_hashrates[thr_id] * 1000.0 : 0.0;
            applog(LOG_DEBUG, "THREAD %d: scanning nonces [%08x..%08x] (%u nonces, ~%.1fms) job=%s",
                   thr_id, work.data[19], max_nonce,
                   (uint32_t)(max_nonce - work.data[19]),
                   estimated_time_ms,
                   work.job_id ? work.job_id : "(null)");
        }

        /* Temporarily disable restart interruption if we haven't had enough time */
        struct timeval now;
        gettimeofday(&now, NULL);
        double elapsed_ms = (now.tv_sec - work_start_time.tv_sec) * 1000.0 +
                           (now.tv_usec - work_start_time.tv_usec) / 1000.0;
        unsigned long saved_restart = 0;
        const double min_work_time_ms = 500.0; // Allow at least 500ms before honoring restarts

        if (elapsed_ms < min_work_time_ms && work_restart[thr_id].restart) {
            saved_restart = work_restart[thr_id].restart;
            work_restart[thr_id].restart = 0;  // Temporarily disable restart
            applog(LOG_DEBUG, "THREAD %d: Temporarily disabled restart after %.1fms (target: %.1fms)",
                   thr_id, elapsed_ms, min_work_time_ms);
        }

        /* scan nonces for a proof-of-work hash with integrated version rolling */
        uint32_t version_mask = work.version_mask;
        uint32_t base_version = work.data[0] & ~version_mask;
        total_hashes_done = 0;
        if (version_mask) {
            /* Determine how many free bits are available and map counter to mask */
            int free_bits = __builtin_popcount(version_mask);
            uint32_t version_sel = scatter_bits(version_ctr & (free_bits ? ((1u << free_bits) - 1) : 0u), version_mask);
            uint32_t chosen_version = base_version | version_sel;
            work.data[0] = chosen_version;
            work.version_solution = version_sel;
        } else {
            work.version_solution = 0;
        }

        unsigned long chunk_hashes = 0;
        switch (opt_algo) {
        case ALGO_SCRYPT:
            rc = scanhash_scrypt(thr_id, work.data, scratchbuf, work.target,
                                  max_nonce, &chunk_hashes, opt_scrypt_n);
            break;
        case ALGO_SHA256D:
            rc = scanhash_sha256d(thr_id, work.data, work.target,
                                  max_nonce, &chunk_hashes);
            break;
        default:
            goto out;
        }
        total_hashes_done = chunk_hashes;

        /* Advance combined counter for next chunk */
        cur_nonce = max_nonce;
        if (cur_nonce >= end_nonce) {
            cur_nonce = start_nonce; /* wrap nonce slice */
            if (version_mask) {
                version_ctr++;
            }
        }

        /* Restore the restart flag if we temporarily disabled it */
        if (saved_restart) {
            work_restart[thr_id].restart = saved_restart;
            applog(LOG_DEBUG, "THREAD %d: Restored restart flag after scanhash", thr_id);
        }

        /* record scanhash elapsed time */
        gettimeofday(&tv_end, NULL);
        timeval_subtract(&diff, &tv_end, &tv_start);
        if (diff.tv_usec || diff.tv_sec) {
            pthread_mutex_lock(&stats_lock);
            thr_hashrates[thr_id] =
                total_hashes_done / (diff.tv_sec + 1e-6 * diff.tv_usec);
            pthread_mutex_unlock(&stats_lock);
        }
        if (opt_debug) {
            sprintf(s, thr_hashrates[thr_id] >= 1e6 ? "%.0f" : "%.2f",
                1e-3 * thr_hashrates[thr_id]);
            applog(LOG_INFO, "thread %d: %lu hashes, %s khash/s",
                thr_id, total_hashes_done, s);
        }

        /* Periodically show full 256-bit target and global best recent hash.
           Only thread 0 prints to avoid spam. */
        if (thr_id == 0) {
            time_t now_ts = time(NULL);
            const int best_log_interval = 5; /* seconds */
            if (now_ts - g_last_best_log >= best_log_interval) {
                unsigned char target_be[32], best_be[32];
                char target_hex[65];
                char best_hex_or_none[65];
                for (int wi = 0; wi < 8; wi++)
                    be32enc((uint32_t *)(target_be + 4 * wi), work.target[7 - wi]);
                bin2hex(target_hex, target_be, 32);
                /* Aggregate best across all threads for this interval */
                bool any = false;
                unsigned char agg_best_bytes[32];
                for (int ti = 0; ti < opt_n_threads; ++ti) {
                    if (thr_best_set && thr_best_set[ti]) {
                        unsigned char *cand_bytes = thr_best_digest_bytes[ti];
                        if (!any || memcmp(cand_bytes, agg_best_bytes, 32) < 0)
                            memcpy(agg_best_bytes, cand_bytes, 32);
                        thr_best_set[ti] = false; /* reset */
                        any = true;
                    }
                }
                if (any) {
                    bin2hex(best_hex_or_none, agg_best_bytes, 32);
                } else {
                    strcpy(best_hex_or_none, "(none)");
                }
                /* Print on separate lines for alignment */
                //applog(LOG_INFO, "target: %s", target_hex);
                applog(LOG_INFO, "best  : %s", best_hex_or_none);
                g_last_best_log = now_ts;
            }
        }
        if (thr_id == opt_n_threads - 1) {
            double hashrate = 0.;
            for (i = 0; i < opt_n_threads && thr_hashrates[i]; i++)
                hashrate += thr_hashrates[i];
            if (i == opt_n_threads) {
                sprintf(s, hashrate >= 1e6 ? "%.0f" : "%.2f", 1e-3 * hashrate);
                applog(LOG_INFO, "Total: %s khash/s", s);
            }
        }

        /* if nonce found, submit work */
        if (rc && !opt_benchmark && !submit_work(mythr, &work))
            break;
    }

out:
    tq_freeze(mythr->q);

    return NULL;
}

static void restart_threads(void)
{
    int i;

    applog(LOG_DEBUG, "RESTART: Setting restart flag for all %d threads", opt_n_threads);
    for (i = 0; i < opt_n_threads;
            i++)
        work_restart[i].restart = 1;
}

static void *longpoll_thread(void *userdata)
{
    struct thr_info *mythr = userdata;
    CURL *curl = NULL;
    char *copy_start, *hdr_path = NULL, *lp_url = NULL;
    bool need_slash = false;

    curl = curl_easy_init();
    if (unlikely(!curl)) {
        applog(LOG_ERR, "CURL initialization failed");
        goto out;
    }

start:
    hdr_path = tq_pop(mythr->q, NULL);
    if (!hdr_path)
        goto out;

    /* full URL */
    if (strstr(hdr_path, "://")) {
        lp_url = hdr_path;
        hdr_path = NULL;
    }

    /* absolute path, on current server */
    else {
        copy_start = (*hdr_path == '/') ? (hdr_path + 1) : hdr_path;
        if (rpc_url[strlen(rpc_url) - 1] != '/')
            need_slash = true;

        lp_url = malloc(strlen(rpc_url) + strlen(copy_start) + 2);
        if (!lp_url)
            goto out;

        sprintf(lp_url, "%s%s%s", rpc_url, need_slash ? "/" : "", copy_start);
    }

    applog(LOG_INFO, "Long-polling activated for %s", lp_url);

    while (1) {
        json_t *val, *res, *soval;
        char *req = NULL;
        int err;

        if (have_gbt) {
            req = malloc(strlen(gbt_lp_req) + strlen(lp_id) + 1);
            sprintf(req, gbt_lp_req, lp_id);
        }
        val = json_rpc_call(curl, lp_url, rpc_userpass,
                    req ? req : getwork_req, &err,
                    JSON_RPC_LONGPOLL);
        free(req);
        if (have_stratum) {
            if (val)
                json_decref(val);
            goto out;
        }
        if (likely(val)) {
            bool rc;
            applog(LOG_INFO, "LONGPOLL pushed new work");
            res = json_object_get(val, "result");
            soval = json_object_get(res, "submitold");
            submit_old = soval ? json_is_true(soval) : false;
            pthread_mutex_lock(&g_work_lock);
            work_free(&g_work);
            if (have_gbt)
                rc = gbt_work_decode(res, &g_work);
            else
                rc = work_decode(res, &g_work);
            if (rc) {
                time(&g_work_time);
                restart_threads();
            }
            pthread_mutex_unlock(&g_work_lock);
            json_decref(val);
        } else {
            pthread_mutex_lock(&g_work_lock);
            g_work_time -= LP_SCANTIME;
            pthread_mutex_unlock(&g_work_lock);
            if (err == CURLE_OPERATION_TIMEDOUT) {
                restart_threads();
            } else {
                have_longpoll = false;
                restart_threads();
                free(hdr_path);
                free(lp_url);
                lp_url = NULL;
                sleep(opt_fail_pause);
                goto start;
            }
        }
    }

out:
    free(hdr_path);
    free(lp_url);
    tq_freeze(mythr->q);
    if (curl)
        curl_easy_cleanup(curl);

    return NULL;
}

static bool stratum_handle_response(char *buf)
{
    json_t *val, *err_val, *res_val, *id_val;
    json_error_t err;
    bool ret = false;

    val = JSON_LOADS(buf, &err);
    if (!val) {
        applog(LOG_INFO, "JSON decode failed(%d): %s", err.line, err.text);
        goto out;
    }

    res_val = json_object_get(val, "result");
            err_val = json_object_get(val, "error");
            id_val = json_object_get(val, "id");

    if (id_val && json_is_integer(id_val) && json_integer_value(id_val) == 10) { /* mining.configure response */
        json_t *result = json_object_get(val, "result");
        json_t *vr_confirmed = json_object_get(result, "version-rolling");
        if (json_is_true(vr_confirmed)) {
            json_t *mask_obj = json_object_get(result, "version-rolling.mask");
            const char *mask_str = json_string_value(mask_obj);
            if (mask_str) {
                applog(LOG_INFO, "version-rolling enabled with mask %s", mask_str);
                /* Pools may send decimal or hex; use base 0 for auto-detect */
                stratum.job.version_mask = strtoul(mask_str, NULL, 0);
            }
        }
        ret = true;
        goto out;
    }

    if (!id_val || json_is_null(id_val) || !res_val)
        goto out;

    share_result(json_is_true(res_val),
        err_val ? json_string_value(json_array_get(err_val, 1)) : NULL);

    ret = true;
out:
    if (val)
        json_decref(val);

    return ret;
}

static void *stratum_thread(void *userdata)
{
    struct thr_info *mythr = userdata;
    char *s;

    stratum.url = tq_pop(mythr->q, NULL);
    if (!stratum.url)
        goto out;
    applog(LOG_INFO, "Starting Stratum on %s", stratum.url);

    while (1) {
        int failures = 0;
        time_t last_recv = time(NULL);
        time_t last_ping = 0;

        while (!stratum.curl) {
            pthread_mutex_lock(&g_work_lock);
            g_work_time = 0;
            pthread_mutex_unlock(&g_work_lock);

            if (!stratum_connect(&stratum, stratum.url) ||
                !stratum_subscribe(&stratum) ||
                !stratum_authorize(&stratum, rpc_user, rpc_pass)) {
                stratum_disconnect(&stratum);
                if (opt_retries >= 0 && ++failures > opt_retries) {
                    applog(LOG_ERR, "...terminating workio thread");
                    tq_push(thr_info[work_thr_id].q, NULL);
                    goto out;
                }
                applog(LOG_ERR, "...retry after %d seconds", opt_fail_pause);
                sleep(opt_fail_pause);
            }

            applog(LOG_INFO, "DEBUG: stratum_thread: Checking suggest_difficulty conditions. opt_suggest_difficulty=%d, suggested_difficulty=%.4f, difficulty_suggested=%d",
                opt_suggest_difficulty, suggested_difficulty, difficulty_suggested);

            if (opt_suggest_difficulty && !difficulty_suggested) {
                double sd_value = 1.0;
                if (suggested_difficulty > 0) {
                    //sd_value = suggested_difficulty;
                    applog(LOG_INFO, "Suggesting new difficulty of %.4f", sd_value);
                } else {
                    /* Fallback: no measured hashrate; suggest diff=1.0 */
                    sd_value = 1.0;
                    applog(LOG_INFO, "No measured hashrate; sending default suggest_difficulty diff=%.1f", sd_value);
                }

                char *req;
                json_t *req_json, *params_arr;
                req_json = json_object();
                json_object_set_new(req_json, "id", json_integer(11));
                json_object_set_new(req_json, "method", json_string("mining.suggest_difficulty"));
                params_arr = json_array();
                //json_array_append_new(params_arr, json_real(sd_value));
                json_array_append_new(params_arr, json_integer(1));
                json_object_set_new(req_json, "params", params_arr);
                req = json_dumps(req_json, 0);
                if (opt_protocol)
                    applog(LOG_INFO, "SEND: %s", req);
                bool sent = stratum_send_line(&stratum, req);
                if (!sent) {
                    applog(LOG_ERR, "Failed to send mining.suggest_difficulty; will retry");
                } else {
                    applog(LOG_INFO, "mining.suggest_difficulty sent (diff=%.4f)", sd_value);
                    difficulty_suggested = true;
                }
                free(req);
                json_decref(req_json);
            }

            if (opt_version_mask) {
                char *req;
                json_t *req_json, *params_arr, *features_arr, *params_obj;
                char *vr_mask = opt_version_mask;
                if (strlen(vr_mask) > 2 && vr_mask[0] == '0' && vr_mask[1] == 'x') {
                    vr_mask += 2;
                }
                req_json = json_object();
                json_object_set_new(req_json, "id", json_integer(10));
                json_object_set_new(req_json, "method", json_string("mining.configure"));
                params_arr = json_array();
                features_arr = json_array();
                json_array_append_new(features_arr, json_string("version-rolling"));
                json_array_append_new(params_arr, features_arr);
                params_obj = json_object();
                json_object_set_new(params_obj, "version-rolling.mask", json_string(vr_mask));
                json_array_append_new(params_arr, params_obj);
                json_object_set_new(req_json, "params", params_arr);
                req = json_dumps(req_json, 0);
                if (opt_protocol)
                    applog(LOG_INFO, "SEND: %s", req);
                stratum_send_line(&stratum, req);
                free(req);
                json_decref(req_json);
            }
        }

        if (stratum.job.job_id &&
            (!g_work_time || !g_work.job_id || strcmp(stratum.job.job_id, g_work.job_id))) {
            pthread_mutex_lock(&g_work_lock);
            stratum_gen_work(&stratum, &g_work);
            if (opt_debug_lax_target) {
                /* Override target to an easy value to force submissions (for debugging) */
                for (int wi = 0; wi < 8; wi++) g_work.target[wi] = 0xffffffffu;
                g_work.target[7] = 0x00ffffffu;
            }
            time(&g_work_time);
            pthread_mutex_unlock(&g_work_lock);
            if (opt_debug) {
                applog(LOG_DEBUG, "STRATUM: new job %s, clean=%d, target_top=%08x",
                       stratum.job.job_id ? stratum.job.job_id : "(null)",
                       stratum.job.clean, g_work.target[7]);
            }
            /* Print full 256-bit target as big-endian hex for validation */
            {
                unsigned char tbytes[32];
                char thex[65];
                for (int wi = 0; wi < 8; wi++)
                    be32enc((uint32_t *)(tbytes + 4 * wi), g_work.target[7 - wi]);
                bin2hex(thex, tbytes, 32);
                applog(LOG_INFO, "target: %s", thex);
            }
            if (stratum.job.clean) {
                applog(LOG_INFO, "Stratum requested work restart");
                restart_threads();
            }
        }

        /* Poll for data in small increments, send ping on idle, disconnect after prolonged idle */
        if (!stratum_socket_full(&stratum, 1)) {
            time_t now = time(NULL);
            if (opt_stratum_ping_secs > 0 && now - last_recv >= opt_stratum_ping_secs && now - last_ping >= opt_stratum_ping_secs) {
                /* Send a lightweight ping (mining.get_version) */
                json_t *req_json = json_object();
                json_object_set_new(req_json, "id", json_integer(99));
                json_object_set_new(req_json, "method", json_string("mining.get_version"));
                json_object_set_new(req_json, "params", json_array());
                char *req = json_dumps(req_json, 0);
                if (opt_protocol)
                    applog(LOG_INFO, "PING: %s", req);
                stratum_send_line(&stratum, req);
                free(req);
                json_decref(req_json);
                last_ping = now;
            }
            if (opt_stratum_idle_secs > 0 && time(NULL) - last_recv >= opt_stratum_idle_secs) {
                applog(LOG_ERR, "Stratum idle for %d seconds, reconnecting", opt_stratum_idle_secs);
                stratum_disconnect(&stratum);
            }
            continue;
        }

        s = stratum_recv_line(&stratum);
        if (!s) {
            stratum_disconnect(&stratum);
            applog(LOG_ERR, "Stratum connection interrupted");
            continue;
        }
        if (s[0] == '\0') {
            /* Soft timeout/no data */
            free(s);
            continue;
        }
        last_recv = time(NULL);
        if (!stratum_handle_method(&stratum, s))
            stratum_handle_response(s);
        free(s);
    }

out:
    return NULL;
}

static void show_version_and_exit(void)
{
    printf(PACKAGE_STRING "\n built on " __DATE__ "\n features:"
#if defined(USE_ASM) && defined(__i386__)
        " i386"
#endif
#if defined(USE_ASM) && defined(__x86_64__)
        " x86_64"
        " PHE"
#endif
#if defined(USE_ASM) && (defined(__i386__) || defined(__x86_64__))
        " SSE2"
#endif
#if defined(__x86_64__) && defined(USE_AVX)
        " AVX"
#endif
#if defined(__x86_64__) && defined(USE_AVX2)
        " AVX2"
#endif
#if defined(__x86_64__) && defined(USE_XOP)
        " XOP"
#endif
#if defined(USE_ASM) && defined(__arm__) && defined(__APCS_32__)
        " ARM"
#if defined(__ARM_ARCH_5E__) || defined(__ARM_ARCH_5TE__) || \
            defined(__ARM_ARCH_5TEJ__) || defined(__ARM_ARCH_6__) || \
            defined(__ARM_ARCH_6J__) || defined(__ARM_ARCH_6K__) || \
            defined(__ARM_ARCH_6M__) || defined(__ARM_ARCH_6T2__) || \
            defined(__ARM_ARCH_6Z__) || defined(__ARM_ARCH_6ZK__) || \
            defined(__ARM_ARCH_7__) || \
            defined(__ARM_ARCH_7A__) || defined(__ARM_ARCH_7R__) || \
            defined(__ARM_ARCH_7M__) || defined(__ARM_ARCH_7EM__)
        " ARMv5E"
#endif
#if defined(__ARM_NEON__)
        " NEON"
#endif
#endif
#if defined(USE_ASM) && (defined(__powerpc__) || defined(__ppc__) || defined(__PPC__))
        " PowerPC"
#if defined(__ALTIVEC__)
        " AltiVec"
#endif
#endif
        "\n");

    printf("%s\n", curl_version());
#ifdef JANSSON_VERSION
    printf("libjansson %s\n", JANSSON_VERSION);
#endif
    exit(0);
}

static void show_usage_and_exit(int status, char *pname)
{
    if (status)
        fprintf(stderr, "Try `%%s --help' for more information.\n", pname);
    else
        printf(usage);
    exit(status);
}

static void strhide(char *s)
{
    if (*s) *s++ = 'x';
    while (*s) *s++ = '\0';
}

static void parse_config(json_t *config, char *pname, char *ref);

static void parse_arg(int key, char *arg, char *pname)
{
    char *p;
    int v, i;

    switch(key) {
    case 'a':
        for (i = 0; i < ARRAY_SIZE(algo_names); i++) {
            v = strlen(algo_names[i]);
            if (!strncmp(arg, algo_names[i], v)) {
                if (arg[v] == '\0') {
                    opt_algo = i;
                    break;
                }
                if (arg[v] == ':' && i == ALGO_SCRYPT) {
                    char *ep;
                    v = strtol(arg+v+1, &ep, 10);
                    if (*ep || v & (v-1) || v < 2)
                        continue;
                    opt_algo = i;
                    opt_scrypt_n = v;
                    break;
                }
            }
        }
        if (i == ARRAY_SIZE(algo_names)) {
            fprintf(stderr, "%s: unknown algorithm -- '%s'\n",
                pname, arg);
            show_usage_and_exit(1, pname);
        }
        break;
    case 'B':
        opt_background = true;
        break;
    case 'c': {
        json_error_t err;
        json_t *config = JSON_LOAD_FILE(arg, &err);
        if (!json_is_object(config)) {
            if (err.line < 0)
                fprintf(stderr, "%s: %s\n", pname, err.text);
            else
                fprintf(stderr, "%s: %s:%d: %s\n",
                    pname, arg, err.line, err.text);
            exit(1);
        }
        parse_config(config, pname, arg);
        json_decref(config);
        break;
    }
    case 'q':
        opt_quiet = true;
        break;
    case 'D':
        opt_debug = true;
        break;
    case 'p':
        free(rpc_pass);
        rpc_pass = strdup(arg);
        strhide(arg);
        break;
    case 'P':
        opt_protocol = true;
        break;
    case 'r':
        v = atoi(arg);
        if (v < -1 || v > 9999)    /* sanity check */
            show_usage_and_exit(1, pname);
        opt_retries = v;
        break;
    case 'R':
        v = atoi(arg);
        if (v < 1 || v > 9999)    /* sanity check */
            show_usage_and_exit(1, pname);
        opt_fail_pause = v;
        break;
    case 's':
        v = atoi(arg);
        if (v < 1 || v > 9999)    /* sanity check */
            show_usage_and_exit(1, pname);
        opt_scantime = v;
        break;
    case 'T':
        v = atoi(arg);
        if (v < 1 || v > 99999)    /* sanity check */
            show_usage_and_exit(1, pname);
        opt_timeout = v;
        break;
    case 't':
        v = atoi(arg);
        if (v < 1 || v > 9999)    /* sanity check */
            show_usage_and_exit(1, pname);
        opt_n_threads = v;
        break;
    case 'u':
        free(rpc_user);
        rpc_user = strdup(arg);
        break;
    case 'o': {        /* --url */
        char *ap, *hp;
        ap = strstr(arg, "://");
        ap = ap ? ap + 3 : arg;
        hp = strrchr(arg, '@');
        if (hp) {
            *hp = '\0';
            p = strchr(ap, ':');
            if (p) {
                free(rpc_userpass);
                rpc_userpass = strdup(ap);
                free(rpc_user);
                rpc_user = calloc(p - ap + 1, 1);
                strncpy(rpc_user, ap, p - ap);
                free(rpc_pass);
                rpc_pass = strdup(++p);
                if (*p) *p++ = 'x';
                v = strlen(hp + 1) + 1;
                memmove(p + 1, hp + 1, v);
                memset(p + v, 0, hp - p);
                hp = p;
            } else {
                free(rpc_user);
                rpc_user = strdup(ap);
            }
            *hp++ = '@';
        } else
            hp = ap;
        if (ap != arg) {
            if (strncasecmp(arg, "http://", 7) &&
                strncasecmp(arg, "https://", 8) &&
                strncasecmp(arg, "stratum+tcp://", 14) &&
                strncasecmp(arg, "stratum+tcps://", 15)) {
                fprintf(stderr, "%s: unknown protocol -- '%s'\n",
                    pname, arg);
                show_usage_and_exit(1, pname);
            }
            free(rpc_url);
            rpc_url = strdup(arg);
            strcpy(rpc_url + (ap - arg), hp);
        } else {
            if (*hp == '\0' || *hp == '/') {
                fprintf(stderr, "%s: invalid URL -- '%s'\n",
                    pname, arg);
                show_usage_and_exit(1, pname);
            }
            free(rpc_url);
            rpc_url = malloc(strlen(hp) + 8);
            sprintf(rpc_url, "http://%s", hp);
        }
        have_stratum = !opt_benchmark && !strncasecmp(rpc_url, "stratum", 7);
        break;
    }
    case 'O':        /* --userpass */
        p = strchr(arg, ':');
        if (!p) {
            fprintf(stderr, "%s: invalid username:password pair -- '%s'\n",
                pname, arg);
            show_usage_and_exit(1, pname);
        }
        free(rpc_userpass);
        rpc_userpass = strdup(arg);
        free(rpc_user);
        rpc_user = calloc(p - arg + 1, 1);
        strncpy(rpc_user, arg, p - arg);
        free(rpc_pass);
        rpc_pass = strdup(++p);
        strhide(p);
        break;
    case 'x':        /* --proxy */
        if (!strncasecmp(arg, "socks4://", 9))
            opt_proxy_type = CURLPROXY_SOCKS4;
        else if (!strncasecmp(arg, "socks5://", 9))
            opt_proxy_type = CURLPROXY_SOCKS5;
#if LIBCURL_VERSION_NUM >= 0x071200
        else if (!strncasecmp(arg, "socks4a://", 10))
            opt_proxy_type = CURLPROXY_SOCKS4A;
        else if (!strncasecmp(arg, "socks5h://", 10))
            opt_proxy_type = CURLPROXY_SOCKS5_HOSTNAME;
#endif
        else
            opt_proxy_type = CURLPROXY_HTTP;
        free(opt_proxy);
        opt_proxy = strdup(arg);
        break;
    case 1001:
        free(opt_cert);
        opt_cert = strdup(arg);
        break;
    case 1005:
        opt_benchmark = true;
        break;
    case 1003:
        want_longpoll = false;
        break;
    case 1007:
        want_stratum = false;
        break;
    case 1009:
        opt_redirect = false;
        break;
    case 1010:
        allow_getwork = false;
        break;
    case 1011:
        have_gbt = false;
        break;
    case 1013:        /* --coinbase-addr */
        pk_script_size = address_to_script(pk_script, sizeof(pk_script), arg);
        if (!pk_script_size) {
            fprintf(stderr, "%s: invalid address -- '%s'\n",
                pname, arg);
            show_usage_and_exit(1, pname);
        }
        break;
    case 1015:        /* --coinbase-sig */
        if (strlen(arg) + 1 > sizeof(coinbase_sig)) {
            fprintf(stderr, "%s: coinbase signature too long\n", pname);
            show_usage_and_exit(1, pname);
        }
        strcpy(coinbase_sig, arg);
        break;
    case 1016:
        opt_version_mask = strdup(arg);
        break;
    case 1017:
        opt_suggest_difficulty = true;
        break;
    case 1018:
        v = atoi(arg);
        if (v < 0 || v > 86400) show_usage_and_exit(1, pname);
        opt_stratum_idle_secs = v;
        break;
    case 1019:
        v = atoi(arg);
        if (v < 0 || v > 86400) show_usage_and_exit(1, pname);
        opt_stratum_ping_secs = v;
        break;
    case 1020:
        opt_debug_sample_canonical = true;
        break;
    case 1021:
        opt_debug_lax_target = true;
        break;
    case 1022:
        opt_debug_merkle_both = true;
        break;
    case 'S':
        use_syslog = true;
        break;
    case 'V':
        show_version_and_exit();
    case 'h':
        show_usage_and_exit(0, pname);
    default:
        show_usage_and_exit(1, pname);
    }
}

static void parse_config(json_t *config, char *pname, char *ref)
{
    int i;
    char *s;
    json_t *val;

    for (i = 0; i < ARRAY_SIZE(options); i++) {
        if (!options[i].name)
            break;

        val = json_object_get(config, options[i].name);
        if (!val)
            continue;

        if (options[i].has_arg && json_is_string(val)) {
            if (!strcmp(options[i].name, "config")) {
                fprintf(stderr, "%s: %s: option '%s' not allowed here\n",
                    pname, ref, options[i].name);
                exit(1);
            }
            s = strdup(json_string_value(val));
            if (!s)
                break;
            parse_arg(options[i].val, s, pname);
            free(s);
        } else if (!options[i].has_arg && json_is_true(val)) {
            parse_arg(options[i].val, "", pname);
        } else {
            fprintf(stderr, "%s: invalid argument for option '%s'\n",
                pname, options[i].name);
            exit(1);
        }
    }
}

static void parse_cmdline(int argc, char *argv[])
{
    int key;

    while (1) {
#if HAVE_GETOPT_LONG
        key = getopt_long(argc, argv, short_options, options, NULL);
#else
        key = getopt(argc, argv, short_options);
#endif
        if (key < 0)
            break;

        parse_arg(key, optarg, argv[0]);
    }
    if (optind < argc) {
        fprintf(stderr, "%s: unsupported non-option argument -- '%s'\n",
            argv[0], argv[optind]);
        show_usage_and_exit(1, argv[0]);
    }
}

#ifndef WIN32
static void signal_handler(int sig)
{
    switch (sig) {
    case SIGHUP:
        applog(LOG_INFO, "SIGHUP received");
        break;
    case SIGINT:
        applog(LOG_INFO, "SIGINT received, exiting");
        exit(0);
        break;
    case SIGTERM:
        applog(LOG_INFO, "SIGTERM received, exiting");
        exit(0);
        break;
    }
}
#endif

int main(int argc, char *argv[])
{
    struct thr_info *thr;
    long flags;
    int i;

    rpc_user = strdup("");
    rpc_pass = strdup("");

    /* parse command line */
    parse_cmdline(argc, argv);

#if defined(WIN32)
    SYSTEM_INFO sysinfo;
    GetSystemInfo(&sysinfo);
    num_processors = sysinfo.dwNumberOfProcessors;
#elif defined(_SC_NPROCESSORS_CONF)
    num_processors = sysconf(_SC_NPROCESSORS_CONF);
#elif defined(CTL_HW) && defined(HW_NCPU)
    int req[] = { CTL_HW, HW_NCPU };
    size_t len = sizeof(num_processors);
    sysctl(req, 2, &num_processors, &len, NULL, 0);
#else
    num_processors = 1;
#endif
    if (num_processors < 1)
        num_processors = 1;
    if (!opt_n_threads)
        opt_n_threads = num_processors;

    /* Run a short CPUNet hashing self-check before starting work threads. */
    if (!cpunet_selfcheck()) {
        applog(LOG_ERR, "CPUNet hashing self-check FAILED; exiting");
        return 1;
    }

    if (opt_suggest_difficulty && !opt_benchmark) {
        /* Run a one-time startup benchmark to estimate hashrate, but do NOT
         * keep benchmark mode enabled during mining (it suppresses submits). */
        opt_benchmark = true;
        applog(LOG_INFO, "Enabling one-time benchmark for difficulty suggestion");
    }

    if (opt_benchmark && !opt_suggest_difficulty) {
        want_longpoll = false;
        want_stratum = false;
        have_stratum = false;
    }

    if (!opt_benchmark && !rpc_url) {
        fprintf(stderr, "%s: no URL supplied\n", argv[0]);
        show_usage_and_exit(1, argv[0]);
    }

    if (!rpc_userpass) {
        rpc_userpass = malloc(strlen(rpc_user) + strlen(rpc_pass) + 2);
        if (!rpc_userpass)
            return 1;
        sprintf(rpc_userpass, "%s:%s", rpc_user, rpc_pass);
    }

    pthread_mutex_init(&applog_lock, NULL);
    pthread_mutex_init(&stats_lock, NULL);
    pthread_mutex_init(&g_work_lock, NULL);
    pthread_mutex_init(&stratum.sock_lock, NULL);
    pthread_mutex_init(&stratum.work_lock, NULL);

    // Initialize benchmark synchronization barriers
    pthread_barrier_init(&benchmark_sync.start_barrier, NULL, opt_n_threads + 1); // +1 for main thread
    pthread_barrier_init(&benchmark_sync.finish_barrier, NULL, opt_n_threads + 1);

    flags = opt_benchmark || (strncasecmp(rpc_url, "https://", 8) &&
                              strncasecmp(rpc_url, "stratum+tcps://", 15))
          ? (CURL_GLOBAL_ALL & ~CURL_GLOBAL_SSL)
          : CURL_GLOBAL_ALL;
    if (curl_global_init(flags)) {
        applog(LOG_ERR, "CURL initialization failed");
        return 1;
    }

#ifndef WIN32
    if (opt_background) {
        i = fork();
        if (i < 0) exit(1);
        if (i > 0) exit(0);
        i = setsid();
        if (i < 0)
            applog(LOG_ERR, "setsid() failed (errno = %d)", errno);
        i = chdir("/");
        if (i < 0)
            applog(LOG_ERR, "chdir() failed (errno = %d)", errno);
        signal(SIGHUP, signal_handler);
        signal(SIGINT, signal_handler);
        signal(SIGTERM, signal_handler);
    }
#endif

#ifdef HAVE_SYSLOG_H
    if (use_syslog)
        openlog("cpuminer", LOG_PID, LOG_USER);
#endif

    work_restart = calloc(opt_n_threads, sizeof(*work_restart));
    if (!work_restart)
        return 1;

    thr_info = calloc(opt_n_threads + 3, sizeof(*thr));
    if (!thr_info)
        return 1;

    thr_hashrates = (double *) calloc(opt_n_threads, sizeof(double));
    if (!thr_hashrates)
        return 1;

    /* allocate best-hash tracking and initialize logger timestamp */
    thr_best_header = calloc(opt_n_threads, sizeof(*thr_best_header));
    thr_best_top_hint = calloc(opt_n_threads, sizeof(*thr_best_top_hint));
    thr_best_digest_bytes = calloc(opt_n_threads, sizeof(*thr_best_digest_bytes));
    thr_best_set = calloc(opt_n_threads, sizeof(*thr_best_set));
    if (!thr_best_header || !thr_best_top_hint || !thr_best_digest_bytes || !thr_best_set)
        return 1;
    /* initialize global best-log timestamp */
    g_last_best_log = time(NULL);

    // Initialize thr_info (id and q for all threads)
    for (i = 0; i < opt_n_threads + 3; i++) {
        thr = &thr_info[i];
        thr->id = i;
        thr->q = tq_new();
        if (!thr->q)
            return 1;
    }

    work_thr_id = opt_n_threads;
    longpoll_thr_id = opt_n_threads + 1;
    stratum_thr_id = opt_n_threads + 2;

    // Create all miner threads
    for (i = 0; i < opt_n_threads; i++) {
        thr = &thr_info[i];
        if (pthread_create(&thr->pth, NULL, miner_thread, thr)) {
            applog(LOG_ERR, "thread %d create failed", i);
            return 1;
        }
    }

    // Always run startup benchmark for 1 second
    run_startup_benchmark();

    // If we only enabled benchmark due to --suggest-difficulty, disable it now
    // so mining threads will submit shares.
    if (opt_suggest_difficulty && opt_benchmark) {
        opt_benchmark = false;
        applog(LOG_INFO, "Disabling benchmark mode; proceeding with normal mining");
    }

    // If only benchmarking (no URL provided), exit after benchmark
    if (opt_benchmark && !rpc_url) {
        applog(LOG_INFO, "Benchmark-only mode, exiting");
        for (i = 0; i < opt_n_threads; i++)
            work_restart[i].restart = 1;
        for (i = 0; i < opt_n_threads; i++)
            pthread_join(thr_info[i].pth, NULL);
        return 0;
    }

    // Start workio thread
    if (pthread_create(&thr_info[work_thr_id].pth, NULL, workio_thread, &thr_info[work_thr_id])) {
        applog(LOG_ERR, "workio thread create failed");
        return 1;
    }

    // Start longpoll thread
    if (want_longpoll && !have_stratum) {
        if (unlikely(pthread_create(&thr_info[longpoll_thr_id].pth, NULL, longpoll_thread, &thr_info[longpoll_thr_id]))) {
            applog(LOG_ERR, "longpoll thread create failed");
            return 1;
        }
    }

    // Start stratum thread
    if (want_stratum) {
        if (unlikely(pthread_create(&thr_info[stratum_thr_id].pth, NULL, stratum_thread, &thr_info[stratum_thr_id]))) {
            applog(LOG_ERR, "stratum thread create failed");
            return 1;
        }
        if (have_stratum)
            tq_push(thr_info[stratum_thr_id].q, strdup(rpc_url));
    }

    applog(LOG_INFO, PACKAGE_STRING " starting");

    /* wait for work I/O thread to terminate */
    thr = &thr_info[work_thr_id];
    pthread_join(thr->pth, NULL);

    applog(LOG_INFO, "workio thread terminated");

    for (i = 0; i < opt_n_threads; i++) {
        thr = &thr_info[i];
        tq_freeze(thr->q);
        pthread_join(thr->pth, NULL);
    }

    applog(LOG_INFO, "miner threads terminated");

    curl_global_cleanup();
    if (use_syslog)
        closelog();

    return 0;
}
