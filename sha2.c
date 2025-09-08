/*
 * Copyright 2011 ArtForz
 * Copyright 2011-2013 pooler
 *
 * This program is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by the Free
 * Software Foundation; either version 2 of the License, or (at your option)
 * any later version.  See COPYING for more details.
 */

#include "cpuminer-config.h"
#include "miner.h"

#include <string.h>
#include <inttypes.h>
#include <immintrin.h>

/* Forward decls for CPU feature checks used before their definitions */
#if defined(__x86_64__)
static inline int cpu_has_avx(void);
#endif

/* cpunet string data */
static const uint32_t cpunet_block2_part[] = {
    0x6370756e, /* bytes: 'c','p','u','n' (big-endian word) */
    0x65740080, /* bytes: 'e','t','\0',0x80 (pad bit) */
};
static const uint32_t cpunet_preimage_len_bits = 87 * 8;

/* Build the full second 512-bit block for CPUNet hashing.
 * Input:  pdata  - 80-byte header as 20 uint32_t words (little-endian miner layout)
 * Output: block2 - 16 words representing the second 64-byte block:
 *                  words [0..3]  = last 16 bytes of the 80-byte header
 *                  words [4..5]  = "cpunet\0" + 0x80 pad bit
 *                  words [6..13] = zeros
 *                  word  [14]    = 0
 *                  word  [15]    = total bit length (80+7 bytes = 696 bits)
 */
void cpunet_build_block2(uint32_t *block2, const uint32_t *pdata)
{
    /* Copy header tail (words 16..19) into words 0..3 */
    memcpy(block2, pdata + 16, 16); /* 16 bytes = 4 words */
    /* Insert CPUNet marker and padding */
    block2[4] = cpunet_block2_part[0];
    block2[5] = cpunet_block2_part[1];
    memset(block2 + 6, 0, (14 - 6) * sizeof(uint32_t));
    block2[14] = 0;
    block2[15] = cpunet_preimage_len_bits;
}

/* Serialize the 80-byte header and CPUNet marker into the canonical 87-byte
 * preimage: header words are little-endian serialized, then "cpunet\0".
 */
void cpunet_serialize_preimage(unsigned char *out87, const uint32_t *header20)
{
    for (int i = 0; i < 20; i++)
        le32enc(out87 + 4 * i, header20[i]);
    /* Append "cpunet" (6 bytes) and a trailing NUL (1 byte) */
    memcpy(out87 + 80, "cpunet\0", 7);
}

/* Debug helper: recompute canonical CPUNet digest for a given header+nonce,
 * print it, and return whether it meets the target via fulltest(). */
static bool cpunet_validate_and_print(int lane, const uint32_t *pdata, uint32_t nonce, const uint32_t *ptarget)
{
    uint32_t header_copy[20];
    memcpy(header_copy, pdata, 80);
    header_copy[19] = nonce;
    unsigned char preimage[87], digest[32];
    cpunet_serialize_preimage(preimage, header_copy);
    sha256d(digest, preimage, sizeof(preimage));
    if(opt_debug) {
        printf("DEBUG: Validating lane %d with fast-path digest...\n", lane);
        printf("Final validation hash: ");
        for (int j = 0; j < 32; j++) printf("%02x", digest[j]);
        printf("\n");
    }
    uint32_t canon_words[8];
    for (int j = 0; j < 8; j++) canon_words[j] = swab32(be32dec(digest + 4 * j));
    if(opt_debug) {
        printf("Final top word:     %08x\n", canon_words[7]);
    }
    return fulltest(canon_words, ptarget);
}


#if defined(USE_ASM) && \
    (defined(__x86_64__) || \
     (defined(__arm__) && defined(__APCS_32__)) || \
     (defined(__powerpc__) || defined(__ppc__) || defined(__PPC__)))
#define EXTERN_SHA256
#endif

static const uint32_t sha256_h[8] = {
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
};

static const uint32_t sha256_k[64] = {
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
    0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
    0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
    0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
    0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
    0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
    0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
    0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
    0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
};

void sha256_init(uint32_t *state)
{
    memcpy(state, sha256_h, 32);
}

/* Elementary functions used by SHA256 */
#define Ch(x, y, z)     ((x & (y ^ z)) ^ z)
#define Maj(x, y, z)    ((x & (y | z)) | (y & z))
#define ROTR(x, n)      ((x >> n) | (x << (32 - n)))
#define S0(x)           (ROTR(x, 2) ^ ROTR(x, 13) ^ ROTR(x, 22))
#define S1(x)           (ROTR(x, 6) ^ ROTR(x, 11) ^ ROTR(x, 25))
#define s0(x)           (ROTR(x, 7) ^ ROTR(x, 18) ^ (x >> 3))
#define s1(x)           (ROTR(x, 17) ^ ROTR(x, 19) ^ (x >> 10))

/* SHA256 round function */
#define RND(a, b, c, d, e, f, g, h, k) \
    do { \
        t0 = h + S1(e) + Ch(e, f, g) + k; \
        t1 = S0(a) + Maj(a, b, c); \
        d += t0; \
        h  = t0 + t1; \
    } while (0)

/* Adjusted round function for rotating state */
#define RNDr(S, W, i) \
    RND(S[(64 - i) % 8], S[(65 - i) % 8], \
        S[(66 - i) % 8], S[(67 - i) % 8], \
        S[(68 - i) % 8], S[(69 - i) % 8], \
        S[(70 - i) % 8], S[(71 - i) % 8], \
        W[i] + sha256_k[i])

#ifndef EXTERN_SHA256

/*
 * SHA256 block compression function.  The 256-bit state is transformed via
 * the 512-bit input block to produce a new state.
 */
void sha256_transform(uint32_t *state, const uint32_t *block, int swap)
{
    uint32_t W[64];
    uint32_t S[8];
    uint32_t t0, t1;
    int i;

    /* 1. Prepare message schedule W. */
    if (swap) {
        for (i = 0; i < 16; i++)
            W[i] = swab32(block[i]);
    } else
        memcpy(W, block, 64);
    for (i = 16; i < 64; i += 2) {
        W[i]   = s1(W[i - 2]) + W[i - 7] + s0(W[i - 15]) + W[i - 16];
        W[i+1] = s1(W[i - 1]) + W[i - 6] + s0(W[i - 14]) + W[i - 15];
    }

    /* 2. Initialize working variables. */
    memcpy(S, state, 32);

    /* 3. Mix. */
    RNDr(S, W,  0);
    RNDr(S, W,  1);
    RNDr(S, W,  2);
    RNDr(S, W,  3);
    RNDr(S, W,  4);
    RNDr(S, W,  5);
    RNDr(S, W,  6);
    RNDr(S, W,  7);
    RNDr(S, W,  8);
    RNDr(S, W,  9);
    RNDr(S, W, 10);
    RNDr(S, W, 11);
    RNDr(S, W, 12);
    RNDr(S, W, 13);
    RNDr(S, W, 14);
    RNDr(S, W, 15);
    RNDr(S, W, 16);
    RNDr(S, W, 17);
    RNDr(S, W, 18);
    RNDr(S, W, 19);
    RNDr(S, W, 20);
    RNDr(S, W, 21);
    RNDr(S, W, 22);
    RNDr(S, W, 23);
    RNDr(S, W, 24);
    RNDr(S, W, 25);
    RNDr(S, W, 26);
    RNDr(S, W, 27);
    RNDr(S, W, 28);
    RNDr(S, W, 29);
    RNDr(S, W, 30);
    RNDr(S, W, 31);
    RNDr(S, W, 32);
    RNDr(S, W, 33);
    RNDr(S, W, 34);
    RNDr(S, W, 35);
    RNDr(S, W, 36);
    RNDr(S, W, 37);
    RNDr(S, W, 38);
    RNDr(S, W, 39);
    RNDr(S, W, 40);
    RNDr(S, W, 41);
    RNDr(S, W, 42);
    RNDr(S, W, 43);
    RNDr(S, W, 44);
    RNDr(S, W, 45);
    RNDr(S, W, 46);
    RNDr(S, W, 47);
    RNDr(S, W, 48);
    RNDr(S, W, 49);
    RNDr(S, W, 50);
    RNDr(S, W, 51);
    RNDr(S, W, 52);
    RNDr(S, W, 53);
    RNDr(S, W, 54);
    RNDr(S, W, 55);
    RNDr(S, W, 56);
    RNDr(S, W, 57);
    RNDr(S, W, 58);
    RNDr(S, W, 59);
    RNDr(S, W, 60);
    RNDr(S, W, 61);
    RNDr(S, W, 62);
    RNDr(S, W, 63);

    /* 4. Mix local working variables into global state */
    for (i = 0; i < 8; i++)
        state[i] += S[i];
}

#endif /* EXTERN_SHA256 */

/* Forward declarations for wrapper below */
#if defined(__x86_64__) && defined(USE_ASM)
void sha256d_ms_phe(uint32_t *hash, uint32_t *W,
    const uint32_t *midstate, const uint32_t *prehash);
#endif
static inline void sha256d_ms_c(uint32_t *hash, uint32_t *W,
    const uint32_t *midstate, const uint32_t *prehash);

/* Reference C compressor (always available) for benchmarking */
static void sha256_transform_ref(uint32_t *state, const uint32_t *block, int swap)
{
    uint32_t W[64];
    uint32_t S[8];
    uint32_t t0, t1;
    int i;

    if (swap) {
        for (i = 0; i < 16; i++)
            W[i] = swab32(block[i]);
    } else
        memcpy(W, block, 64);
    for (i = 16; i < 64; i += 2) {
        W[i]   = s1(W[i - 2]) + W[i - 7] + s0(W[i - 15]) + W[i - 16];
        W[i+1] = s1(W[i - 1]) + W[i - 6] + s0(W[i - 14]) + W[i - 15];
    }

    memcpy(S, state, 32);

    RNDr(S, W,  0); RNDr(S, W,  1); RNDr(S, W,  2); RNDr(S, W,  3);
    RNDr(S, W,  4); RNDr(S, W,  5); RNDr(S, W,  6); RNDr(S, W,  7);
    RNDr(S, W,  8); RNDr(S, W,  9); RNDr(S, W, 10); RNDr(S, W, 11);
    RNDr(S, W, 12); RNDr(S, W, 13); RNDr(S, W, 14); RNDr(S, W, 15);
    RNDr(S, W, 16); RNDr(S, W, 17); RNDr(S, W, 18); RNDr(S, W, 19);
    RNDr(S, W, 20); RNDr(S, W, 21); RNDr(S, W, 22); RNDr(S, W, 23);
    RNDr(S, W, 24); RNDr(S, W, 25); RNDr(S, W, 26); RNDr(S, W, 27);
    RNDr(S, W, 28); RNDr(S, W, 29); RNDr(S, W, 30); RNDr(S, W, 31);
    RNDr(S, W, 32); RNDr(S, W, 33); RNDr(S, W, 34); RNDr(S, W, 35);
    RNDr(S, W, 36); RNDr(S, W, 37); RNDr(S, W, 38); RNDr(S, W, 39);
    RNDr(S, W, 40); RNDr(S, W, 41); RNDr(S, W, 42); RNDr(S, W, 43);
    RNDr(S, W, 44); RNDr(S, W, 45); RNDr(S, W, 46); RNDr(S, W, 47);
    RNDr(S, W, 48); RNDr(S, W, 49); RNDr(S, W, 50); RNDr(S, W, 51);
    RNDr(S, W, 52); RNDr(S, W, 53); RNDr(S, W, 54); RNDr(S, W, 55);
    RNDr(S, W, 56); RNDr(S, W, 57); RNDr(S, W, 58); RNDr(S, W, 59);
    RNDr(S, W, 60); RNDr(S, W, 61); RNDr(S, W, 62); RNDr(S, W, 63);

    for (i = 0; i < 8; i++)
        state[i] += S[i];
}

#if defined(__x86_64__) && defined(USE_ASM)
/* SHA-NI accelerated single-block compressor using scalar schedule + rnds2. */
#if defined(__GNUC__)
__attribute__((target("sha")))
#endif
static void sha256_transform_shani(uint32_t *state, const uint32_t *block, int swap)
{
    uint32_t W[64];
    int i;
    if (swap) {
        for (i = 0; i < 16; i++)
            W[i] = swab32(block[i]);
    } else {
        memcpy(W, block, 64);
    }
    for (i = 16; i < 64; i++)
        W[i] = s1(W[i - 2]) + W[i - 7] + s0(W[i - 15]) + W[i - 16];

    __m128i STATE0 = _mm_loadu_si128((const __m128i *)(state + 0));
    __m128i STATE1 = _mm_loadu_si128((const __m128i *)(state + 4));
    const __m128i SAVE0 = STATE0;
    const __m128i SAVE1 = STATE1;

    for (i = 0; i < 64; i += 4) {
        __m128i MSG = _mm_set_epi32((int)(W[i+3] + sha256_k[i+3]),
                                     (int)(W[i+2] + sha256_k[i+2]),
                                     (int)(W[i+1] + sha256_k[i+1]),
                                     (int)(W[i+0] + sha256_k[i+0]));
        STATE1 = _mm_sha256rnds2_epu32(STATE1, STATE0, MSG);
        MSG = _mm_shuffle_epi32(MSG, 0x0e);
        STATE0 = _mm_sha256rnds2_epu32(STATE0, STATE1, MSG);
    }

    STATE0 = _mm_add_epi32(STATE0, SAVE0);
    STATE1 = _mm_add_epi32(STATE1, SAVE1);
    _mm_storeu_si128((__m128i *)(state + 0), STATE0);
    _mm_storeu_si128((__m128i *)(state + 4), STATE1);
}

static inline
#if defined(__GNUC__)
__attribute__((target("sha")))
#endif
void sha256d_ms_shani(uint32_t *hash, uint32_t *W,
    const uint32_t *midstate, const uint32_t *prehash)
{
    static const uint32_t sha256d_hash1[16];
    uint32_t st1[8];
    memcpy(st1, midstate, 32);
    sha256_transform_shani(st1, W, 0);

    uint32_t blk32[16];
    for (int i2 = 0; i2 < 8; i2++) blk32[i2] = st1[i2];
    memcpy(blk32 + 8, sha256d_hash1 + 8, 32);
    sha256_init(hash);
    sha256_transform_shani(hash, blk32, 0);
}
#endif

static const uint32_t sha256d_hash1[16] = {
    0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x80000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000100
};

/* Debug: verify second-pass W2 schedule and preextension fold-ins for a single header */
static void debug_verify_w2_preext(const uint32_t header20[20])
{
    if (!opt_debug) return;
    uint32_t pdata_be[20];
    for (int i = 0; i < 20; ++i) pdata_be[i] = swab32(header20[i]);
    uint32_t block2[16];
    cpunet_build_block2(block2, pdata_be);
    uint32_t mid[8];
    sha256_init(mid);
    sha256_transform(mid, pdata_be, 0);
    /* First-pass digest words become W2[0..7] */
    uint32_t W2a[64], W2b[64];
    for (int i = 0; i < 8; i++) { W2a[i] = mid[i]; W2b[i] = mid[i]; }
    for (int i = 8; i < 16; i++) { W2a[i] = sha256d_hash1[i]; W2b[i] = sha256d_hash1[i]; }
    for (int i = 16; i < 64; i++) {
        W2a[i] = s1(W2a[i-2]) + W2a[i-7] + s0(W2a[i-15]) + W2a[i-16];
        W2b[i] = s1(W2b[i-2]) + W2b[i-7] + s0(W2b[i-15]) + W2b[i-16];
    }
    /* Apply preextension fold-ins to the scalar schedule for comparison */
    W2b[17] += 0x00a00000u;
    W2b[23] += 0x11002000u;
    W2b[24] += 0x80000000u;
    W2b[30] += 0x00400022u;
    /* Compress both and compare outputs */
    uint32_t Sa[8], Sb[8];
    uint32_t t0 = 0, t1 = 0;
    sha256_init(Sa); sha256_init(Sb);
    for (int r = 0; r < 64; r++) {
        RNDr(Sa, W2a, r);
        RNDr(Sb, W2b, r);
    }
    for (int i = 0; i < 8; i++) { Sa[i] += sha256_h[i]; Sb[i] += sha256_h[i]; }
    int diff = memcmp(Sa, Sb, sizeof(Sa));
    if (diff != 0) {
        applog(LOG_DEBUG, "DEBUG preext2 scalar check mismatch: Sa != Sb");
    } else {
        applog(LOG_DEBUG, "DEBUG preext2 scalar check OK: Sa == Sb");
    }
    /* Print key schedule words for manual mapping */
    applog(LOG_DEBUG, "DEBUG W2[17]=%08x W2[23]=%08x W2[24]=%08x W2[30]=%08x",
           W2a[17], W2a[23], W2a[24], W2a[30]);
}

static void sha256d_80_swap(uint32_t *hash, const uint32_t *data)
{
    uint32_t S[16];
    int i;

    sha256_init(S);
    sha256_transform(S, data, 0);
    sha256_transform(S, data + 16, 0);
    memcpy(S + 8, sha256d_hash1 + 8, 32);
    sha256_init(hash);
    sha256_transform(hash, S, 0);
    for (i = 0; i < 8; i++)
        hash[i] = swab32(hash[i]);
}

/* Compute CPUNet digest via the optimized fast-path for a single header (nonce in pdata[19]). */
/* cpunet_hash_fast and cpunet_selfcheck are defined later, after helpers. */

void sha256d(unsigned char *hash, const unsigned char *data, int len)
{
    uint32_t S[16], T[16];
    int i, r;

    sha256_init(S);
    for (r = len; r > -9; r -= 64) {
        if (r < 64)
            memset(T, 0, 64);
        memcpy(T, data + len - r, r > 64 ? 64 : (r < 0 ? 0 : r));
        if (r >= 0 && r < 64)
            ((unsigned char *)T)[r] = 0x80;
        for (i = 0; i < 16; i++)
            T[i] = be32dec((unsigned char*)T + i*4);
        if (r < 56)
            T[15] = 8 * len;

        sha256_transform(S, T, 0);
    }
    memcpy(S + 8, sha256d_hash1 + 8, 32);
    sha256_init(T);
    sha256_transform(T, S, 0);
    for (i = 0; i < 8; i++)
        be32enc((uint32_t *)hash + i, T[i]);
}


static inline void sha256d_preextend(uint32_t *W)
{
    W[16] = s1(W[14]) + W[ 9] + s0(W[ 1]) + W[ 0];
    W[17] = s1(W[15]) + W[10] + s0(W[ 2]) + W[ 1];
    W[18] = s1(W[16]) + W[11]             + W[ 2];
    W[19] = s1(W[17]) + W[12] + s0(W[ 4]);
    W[20] =             W[13] + s0(W[ 5]) + W[ 4];
    W[21] =             W[14] + s0(W[ 6]) + W[ 5];
    W[22] =             W[15] + s0(W[ 7]) + W[ 6];
    W[23] =             W[16] + s0(W[ 8]) + W[ 7];
    W[24] =             W[17] + s0(W[ 9]) + W[ 8];
    W[25] =                     s0(W[10]) + W[ 9];
    W[26] =                     s0(W[11]) + W[10];
    W[27] =                     s0(W[12]) + W[11];
    W[28] =                     s0(W[13]) + W[12];
    W[29] =                     s0(W[14]) + W[13];
    W[30] =                     s0(W[15]) + W[14];
    W[31] =                     s0(W[16]) + W[15];
}

static inline void sha256d_prehash(uint32_t *S, const uint32_t *W)
{
    uint32_t t0, t1;
    RNDr(S, W, 0);
    RNDr(S, W, 1);
    RNDr(S, W, 2);
}

#if 1
/* Always provide a portable C implementation of sha256d_ms to avoid
 * depending on CPU-specific SHA extensions in the scalar path. */
static inline void sha256d_ms_c(uint32_t *hash, uint32_t *W,
    const uint32_t *midstate, const uint32_t *prehash)
{
    /* Use the generic compression to avoid arch-specific tricks */
    uint32_t st1[8];
    memcpy(st1, midstate, 32);
    sha256_transform_ref(st1, W, 0);

    uint32_t blk32[16];
    for (int i2 = 0; i2 < 8; i2++) blk32[i2] = st1[i2];
    memcpy(blk32 + 8, sha256d_hash1 + 8, 32);
    sha256_init(hash);
    sha256_transform_ref(hash, blk32, 0);
}
#endif
#ifdef EXTERN_SHA256

/* PHE-only assembly version is exposed under a different name. */
void sha256d_ms_phe(uint32_t *hash, uint32_t *W,
    const uint32_t *midstate, const uint32_t *prehash);

#else

/* Keep an optimized reference variant available, but avoid naming clash with
 * the dispatcher above. */
static inline void sha256d_ms_opt(uint32_t *hash, uint32_t *W,
    const uint32_t *midstate, const uint32_t *prehash)
{
    uint32_t S[64];
    uint32_t t0, t1;
    int i;

    S[18] = W[18];
    S[19] = W[19];
    S[20] = W[20];
    S[22] = W[22];
    S[23] = W[23];
    S[24] = W[24];
    S[30] = W[30];
    S[31] = W[31];

    W[18] += s0(W[3]);
    W[19] += W[3];
    W[20] += s1(W[18]);
    W[21]  = s1(W[19]);
    W[22] += s1(W[20]);
    W[23] += s1(W[21]);
    W[24] += s1(W[22]);
    W[25]  = s1(W[23]) + W[18];
    W[26]  = s1(W[24]) + W[19];
    W[27]  = s1(W[25]) + W[20];
    W[28]  = s1(W[26]) + W[21];
    W[29]  = s1(W[27]) + W[22];
    W[30] += s1(W[28]) + W[23];
    W[31] += s1(W[29]) + W[24];
    for (i = 32; i < 64; i += 2) {
        W[i]   = s1(W[i - 2]) + W[i - 7] + s0(W[i - 15]) + W[i - 16];
        W[i+1] = s1(W[i - 1]) + W[i - 6] + s0(W[i - 14]) + W[i - 15];
    }

    memcpy(S, prehash, 32);

    RNDr(S, W,  3);
    RNDr(S, W,  4);
    RNDr(S, W,  5);
    RNDr(S, W,  6);
    RNDr(S, W,  7);
    RNDr(S, W,  8);
    RNDr(S, W,  9);
    RNDr(S, W, 10);
    RNDr(S, W, 11);
    RNDr(S, W, 12);
    RNDr(S, W, 13);
    RNDr(S, W, 14);
    RNDr(S, W, 15);
    RNDr(S, W, 16);
    RNDr(S, W, 17);
    RNDr(S, W, 18);
    RNDr(S, W, 19);
    RNDr(S, W, 20);
    RNDr(S, W, 21);
    RNDr(S, W, 22);
    RNDr(S, W, 23);
    RNDr(S, W, 24);
    RNDr(S, W, 25);
    RNDr(S, W, 26);
    RNDr(S, W, 27);
    RNDr(S, W, 28);
    RNDr(S, W, 29);
    RNDr(S, W, 30);
    RNDr(S, W, 31);
    RNDr(S, W, 32);
    RNDr(S, W, 33);
    RNDr(S, W, 34);
    RNDr(S, W, 35);
    RNDr(S, W, 36);
    RNDr(S, W, 37);
    RNDr(S, W, 38);
    RNDr(S, W, 39);
    RNDr(S, W, 40);
    RNDr(S, W, 41);
    RNDr(S, W, 42);
    RNDr(S, W, 43);
    RNDr(S, W, 44);
    RNDr(S, W, 45);
    RNDr(S, W, 46);
    RNDr(S, W, 47);
    RNDr(S, W, 48);
    RNDr(S, W, 49);
    RNDr(S, W, 50);
    RNDr(S, W, 51);
    RNDr(S, W, 52);
    RNDr(S, W, 53);
    RNDr(S, W, 54);
    RNDr(S, W, 55);
    RNDr(S, W, 56);
    RNDr(S, W, 57);
    RNDr(S, W, 58);
    RNDr(S, W, 59);
    RNDr(S, W, 60);
    RNDr(S, W, 61);
    RNDr(S, W, 62);
    RNDr(S, W, 63);

    for (i = 0; i < 8; i++)
        S[i] += midstate[i];

    W[18] = S[18];
    W[19] = S[19];
    W[20] = S[20];
    W[22] = S[22];
    W[23] = S[23];
    W[24] = S[24];
    W[30] = S[30];
    W[31] = S[31];

    memcpy(S + 8, sha256d_hash1 + 8, 32);
    S[16] = s1(sha256d_hash1[14]) + sha256d_hash1[ 9] + s0(S[ 1]) + S[ 0];
    S[17] = s1(sha256d_hash1[15]) + sha256d_hash1[10] + s0(S[ 2]) + S[ 1];
    S[18] = s1(S[16]) + sha256d_hash1[11] + s0(S[ 3]) + S[ 2];
    S[19] = s1(S[17]) + sha256d_hash1[12] + s0(S[ 4]) + S[ 3];
    S[20] = s1(S[18]) + sha256d_hash1[13] + s0(S[ 5]) + S[ 4];
    S[21] = s1(S[19]) + sha256d_hash1[14] + s0(S[ 6]) + S[ 5];
    S[22] = s1(S[20]) + sha256d_hash1[15] + s0(S[ 7]) + S[ 6];
    S[23] = s1(S[21]) + S[16] + s0(sha256d_hash1[ 8]) + S[ 7];
    S[24] = s1(S[22]) + S[17] + s0(sha256d_hash1[ 9]) + sha256d_hash1[ 8];
    S[25] = s1(S[23]) + S[18] + s0(sha256d_hash1[10]) + sha256d_hash1[ 9];
    S[26] = s1(S[24]) + S[19] + s0(sha256d_hash1[11]) + sha256d_hash1[10];
    S[27] = s1(S[25]) + S[20] + s0(sha256d_hash1[12]) + sha256d_hash1[11];
    S[28] = s1(S[26]) + S[21] + s0(sha256d_hash1[13]) + sha256d_hash1[12];
    S[29] = s1(S[27]) + S[22] + s0(sha256d_hash1[14]) + sha256d_hash1[13];
    S[30] = s1(S[28]) + S[23] + s0(sha256d_hash1[15]) + sha256d_hash1[14];
    S[31] = s1(S[29]) + S[24] + s0(S[16])             + sha256d_hash1[15];
    for (i = 32; i < 60; i += 2) {
        S[i]   = s1(S[i - 2]) + S[i - 7] + s0(S[i - 15]) + S[i - 16];
        S[i+1] = s1(S[i - 1]) + S[i - 6] + s0(S[i - 14]) + S[i - 15];
    }
    S[60] = s1(S[58]) + S[53] + s0(S[45]) + S[44];

    sha256_init(hash);

    RNDr(hash, S,  0);
    RNDr(hash, S,  1);
    RNDr(hash, S,  2);
    RNDr(hash, S,  3);
    RNDr(hash, S,  4);
    RNDr(hash, S,  5);
    RNDr(hash, S,  6);
    RNDr(hash, S,  7);
    RNDr(hash, S,  8);
    RNDr(hash, S,  9);
    RNDr(hash, S, 10);
    RNDr(hash, S, 11);
    RNDr(hash, S, 12);
    RNDr(hash, S, 13);
    RNDr(hash, S, 14);
    RNDr(hash, S, 15);
    RNDr(hash, S, 16);
    RNDr(hash, S, 17);
    RNDr(hash, S, 18);
    RNDr(hash, S, 19);
    RNDr(hash, S, 20);
    RNDr(hash, S, 21);
    RNDr(hash, S, 22);
    RNDr(hash, S, 23);
    RNDr(hash, S, 24);
    RNDr(hash, S, 25);
    RNDr(hash, S, 26);
    RNDr(hash, S, 27);
    RNDr(hash, S, 28);
    RNDr(hash, S, 29);
    RNDr(hash, S, 30);
    RNDr(hash, S, 31);
    RNDr(hash, S, 32);
    RNDr(hash, S, 33);
    RNDr(hash, S, 34);
    RNDr(hash, S, 35);
    RNDr(hash, S, 36);
    RNDr(hash, S, 37);
    RNDr(hash, S, 38);
    RNDr(hash, S, 39);
    RNDr(hash, S, 40);
    RNDr(hash, S, 41);
    RNDr(hash, S, 42);
    RNDr(hash, S, 43);
    RNDr(hash, S, 44);
    RNDr(hash, S, 45);
    RNDr(hash, S, 46);
    RNDr(hash, S, 47);
    RNDr(hash, S, 48);
    RNDr(hash, S, 49);
    RNDr(hash, S, 50);
    RNDr(hash, S, 51);
    RNDr(hash, S, 52);
    RNDr(hash, S, 53);
    RNDr(hash, S, 54);
    RNDr(hash, S, 55);
    RNDr(hash, S, 56);

    hash[2] += hash[6] + S1(hash[3]) + Ch(hash[3], hash[4], hash[5])
             + S[57] + sha256_k[57];
    hash[1] += hash[5] + S1(hash[2]) + Ch(hash[2], hash[3], hash[4])
             + S[58] + sha256_k[58];
    hash[0] += hash[4] + S1(hash[1]) + Ch(hash[1], hash[2], hash[3])
             + S[59] + sha256_k[59];
    hash[7] += hash[3] + S1(hash[0]) + Ch(hash[0], hash[1], hash[2])
             + S[60] + sha256_k[60]
             + sha256_h[7];
}

#endif /* EXTERN_SHA256 */

#ifdef HAVE_SHA256_4WAY

void sha256d_ms_4way(uint32_t *hash,  uint32_t *data,
    const uint32_t *midstate, const uint32_t *prehash);

void sha256d_ms(uint32_t *hash, uint32_t *W,
    const uint32_t *midstate, const uint32_t *prehash);

/* Correctness-first C reference for 4-way: derive each lane from scalar path. */
static inline void sha256d_ms_4way_c(uint32_t *hash, uint32_t *data,
    const uint32_t *midstate, const uint32_t *prehash)
{
    for (int lane = 0; lane < 4; lane++) {
        uint32_t W[64];
        /* gather lane's block words */
        for (int i = 0; i < 16; i++) W[i] = data[i * 4 + lane];
        sha256d_preextend(W);
        uint32_t ms[8], ph[8], out[8];
        for (int i = 0; i < 8; i++) {
            ms[i] = midstate[i * 4 + lane];
            ph[i] = prehash[i * 4 + lane];
        }
        sha256d_ms(out, W, ms, ph);
        for (int i = 0; i < 8; i++) hash[i * 4 + lane] = out[i];
    }
}

/* SSE2 4-way SIMD kernel */
static inline __m128i sse_rotr32(__m128i x, int n) {
    return _mm_or_si128(_mm_srli_epi32(x, n), _mm_slli_epi32(x, 32 - n));
}
static inline __m128i sse_S0(__m128i x) {
    return _mm_xor_si128(_mm_xor_si128(sse_rotr32(x, 2), sse_rotr32(x, 13)), sse_rotr32(x, 22));
}
static inline __m128i sse_S1(__m128i x) {
    return _mm_xor_si128(_mm_xor_si128(sse_rotr32(x, 6), sse_rotr32(x, 11)), sse_rotr32(x, 25));
}
static inline __m128i sse_s0(__m128i x) {
    return _mm_xor_si128(_mm_xor_si128(sse_rotr32(x, 7), sse_rotr32(x, 18)), _mm_srli_epi32(x, 3));
}
static inline __m128i sse_s1(__m128i x) {
    return _mm_xor_si128(_mm_xor_si128(sse_rotr32(x, 17), sse_rotr32(x, 19)), _mm_srli_epi32(x, 10));
}

static void sha256d_ms_4way_simd(uint32_t *hash, uint32_t *data,
    const uint32_t *midstate, const uint32_t *prehash)
{
    /* Pre-broadcasted K constants to avoid set1 in the round loop */
    static __m128i K4[64];
    static int K4_init = 0;
    if (!K4_init) {
        for (int i = 0; i < 64; i++) K4[i] = _mm_set1_epi32((int)sha256_k[i]);
        K4_init = 1;
    }
    __m128i W[16];
    const __m128i *d4 = (const __m128i *) __builtin_assume_aligned(data, 16);
    for (int i = 0; i < 16; i++)
        W[i] = _mm_load_si128(d4 + i);
    __m128i A = _mm_set_epi32((int)midstate[0*4+3], (int)midstate[0*4+2], (int)midstate[0*4+1], (int)midstate[0*4+0]);
    __m128i B = _mm_set_epi32((int)midstate[1*4+3], (int)midstate[1*4+2], (int)midstate[1*4+1], (int)midstate[1*4+0]);
    __m128i C = _mm_set_epi32((int)midstate[2*4+3], (int)midstate[2*4+2], (int)midstate[2*4+1], (int)midstate[2*4+0]);
    __m128i D = _mm_set_epi32((int)midstate[3*4+3], (int)midstate[3*4+2], (int)midstate[3*4+1], (int)midstate[3*4+0]);
    __m128i E = _mm_set_epi32((int)midstate[4*4+3], (int)midstate[4*4+2], (int)midstate[4*4+1], (int)midstate[4*4+0]);
    __m128i F = _mm_set_epi32((int)midstate[5*4+3], (int)midstate[5*4+2], (int)midstate[5*4+1], (int)midstate[5*4+0]);
    __m128i G = _mm_set_epi32((int)midstate[6*4+3], (int)midstate[6*4+2], (int)midstate[6*4+1], (int)midstate[6*4+0]);
    __m128i H = _mm_set_epi32((int)midstate[7*4+3], (int)midstate[7*4+2], (int)midstate[7*4+1], (int)midstate[7*4+0]);
    __m128i SA=A, SB=B, SC=C, SD=D, SE=E, SF=F, SG=G, SH=H;
    #define SSE_ROUND(AA,BB,CC,DD,EE,FF,GG,HH, WT, KI) do { \
        __m128i ch = _mm_xor_si128(_mm_and_si128((EE),(FF)), _mm_andnot_si128((EE),(GG))); \
        __m128i t1 = _mm_add_epi32((HH), _mm_add_epi32(sse_S1(EE), _mm_add_epi32(ch, _mm_add_epi32((WT),(KI))))); \
        __m128i maj = _mm_xor_si128(_mm_xor_si128(_mm_and_si128((AA),(BB)), _mm_and_si128((AA),(CC))), _mm_and_si128((BB),(CC))); \
        __m128i t2 = _mm_add_epi32(sse_S0(AA), maj); \
        (DD) = _mm_add_epi32((DD), t1); \
        (HH) = _mm_add_epi32(t1, t2); \
        __m128i tmp_ = (HH); (HH) = (GG); (GG) = (FF); (FF) = (EE); (EE) = (DD); (DD) = (CC); (CC) = (BB); (BB) = (AA); (AA) = tmp_; \
    } while(0)

    for (int i = 0; i < 64; i += 4) {
        int t0 = (i + 0) & 15; int t1i = (i + 1) & 15; int t2i = (i + 2) & 15; int t3 = (i + 3) & 15;
        if (i >= 16) {
            W[t0] = _mm_add_epi32(_mm_add_epi32(sse_s1(W[(t0 + 14) & 15]), W[(t0 + 9) & 15]), _mm_add_epi32(sse_s0(W[(t0 + 1) & 15]), W[t0]));
            W[t1i] = _mm_add_epi32(_mm_add_epi32(sse_s1(W[(t1i + 14) & 15]), W[(t1i + 9) & 15]), _mm_add_epi32(sse_s0(W[(t1i + 1) & 15]), W[t1i]));
            W[t2i] = _mm_add_epi32(_mm_add_epi32(sse_s1(W[(t2i + 14) & 15]), W[(t2i + 9) & 15]), _mm_add_epi32(sse_s0(W[(t2i + 1) & 15]), W[t2i]));
            W[t3] = _mm_add_epi32(_mm_add_epi32(sse_s1(W[(t3 + 14) & 15]), W[(t3 + 9) & 15]), _mm_add_epi32(sse_s0(W[(t3 + 1) & 15]), W[t3]));
        }
        SSE_ROUND(A,B,C,D,E,F,G,H, W[t0], K4[i+0]);
        SSE_ROUND(A,B,C,D,E,F,G,H, W[t1i], K4[i+1]);
        SSE_ROUND(A,B,C,D,E,F,G,H, W[t2i], K4[i+2]);
        SSE_ROUND(A,B,C,D,E,F,G,H, W[t3], K4[i+3]);
    }
    #undef SSE_ROUND
    A = _mm_add_epi32(A, SA); B = _mm_add_epi32(B, SB); C = _mm_add_epi32(C, SC); D = _mm_add_epi32(D, SD);
    E = _mm_add_epi32(E, SE); F = _mm_add_epi32(F, SF); G = _mm_add_epi32(G, SG); H = _mm_add_epi32(H, SH);

    __m128i W2[16];
    static __m128i P2_17_4, P2_23_4, P2_24_4, P2_30_4; static int P2_4_init=0; static int use_preext2_4=1;
    if (!P2_4_init) { P2_17_4=_mm_set1_epi32(0x00a00000); P2_23_4=_mm_set1_epi32(0x11002000); P2_24_4=_mm_set1_epi32(0x80000000); P2_30_4=_mm_set1_epi32(0x00400022); P2_4_init=1; }
    W2[0]=A; W2[1]=B; W2[2]=C; W2[3]=D; W2[4]=E; W2[5]=F; W2[6]=G; W2[7]=H;
    for (int i = 8; i < 16; i++) W2[i] = _mm_set1_epi32((int)sha256d_hash1[i]);
    A = _mm_set1_epi32((int)sha256_h[0]); B = _mm_set1_epi32((int)sha256_h[1]);
    C = _mm_set1_epi32((int)sha256_h[2]); D = _mm_set1_epi32((int)sha256_h[3]);
    E = _mm_set1_epi32((int)sha256_h[4]); F = _mm_set1_epi32((int)sha256_h[5]);
    G = _mm_set1_epi32((int)sha256_h[6]); H = _mm_set1_epi32((int)sha256_h[7]);
    #define SSE_ROUND2(AA,BB,CC,DD,EE,FF,GG,HH, WT, KI) do { \
        __m128i ch = _mm_xor_si128(_mm_and_si128((EE),(FF)), _mm_andnot_si128((EE),(GG))); \
        __m128i t1 = _mm_add_epi32((HH), _mm_add_epi32(sse_S1(EE), _mm_add_epi32(ch, _mm_add_epi32((WT),(KI))))); \
        __m128i maj = _mm_xor_si128(_mm_xor_si128(_mm_and_si128((AA),(BB)), _mm_and_si128((AA),(CC))), _mm_and_si128((BB),(CC))); \
        __m128i t2 = _mm_add_epi32(sse_S0(AA), maj); \
        (DD) = _mm_add_epi32((DD), t1); \
        (HH) = _mm_add_epi32(t1, t2); \
        __m128i tmp_ = (HH); (HH) = (GG); (GG) = (FF); (FF) = (EE); (EE) = (DD); (DD) = (CC); (CC) = (BB); (BB) = (AA); (AA) = tmp_; \
    } while(0)

    for (int i = 0; i < 64; i += 4) {
        int t0 = (i + 0) & 15; int t1i = (i + 1) & 15; int t2i = (i + 2) & 15; int t3 = (i + 3) & 15;
        if (i >= 16) {
            W2[t0] = _mm_add_epi32(_mm_add_epi32(sse_s1(W2[(t0 + 14) & 15]), W2[(t0 + 9) & 15]), _mm_add_epi32(sse_s0(W2[(t0 + 1) & 15]), W2[t0]));
            if (use_preext2_4) { if (i+0 == 17) W2[t0] = _mm_add_epi32(W2[t0], P2_17_4); }
            W2[t1i] = _mm_add_epi32(_mm_add_epi32(sse_s1(W2[(t1i + 14) & 15]), W2[(t1i + 9) & 15]), _mm_add_epi32(sse_s0(W2[(t1i + 1) & 15]), W2[t1i]));
            if (use_preext2_4) { if (i+1 == 23) W2[t1i] = _mm_add_epi32(W2[t1i], P2_23_4); }
            W2[t2i] = _mm_add_epi32(_mm_add_epi32(sse_s1(W2[(t2i + 14) & 15]), W2[(t2i + 9) & 15]), _mm_add_epi32(sse_s0(W2[(t2i + 1) & 15]), W2[t2i]));
            if (use_preext2_4) { if (i+2 == 24) W2[t2i] = _mm_add_epi32(W2[t2i], P2_24_4); }
            W2[t3] = _mm_add_epi32(_mm_add_epi32(sse_s1(W2[(t3 + 14) & 15]), W2[(t3 + 9) & 15]), _mm_add_epi32(sse_s0(W2[(t3 + 1) & 15]), W2[t3]));
            if (use_preext2_4) { if (i+3 == 30) W2[t3] = _mm_add_epi32(W2[t3], P2_30_4); }
        }
        SSE_ROUND2(A,B,C,D,E,F,G,H, W2[t0], K4[i+0]);
        SSE_ROUND2(A,B,C,D,E,F,G,H, W2[t1i], K4[i+1]);
        SSE_ROUND2(A,B,C,D,E,F,G,H, W2[t2i], K4[i+2]);
        SSE_ROUND2(A,B,C,D,E,F,G,H, W2[t3], K4[i+3]);
    }
    #undef SSE_ROUND2
    A = _mm_add_epi32(A, _mm_set1_epi32((int)sha256_h[0]));
    B = _mm_add_epi32(B, _mm_set1_epi32((int)sha256_h[1]));
    C = _mm_add_epi32(C, _mm_set1_epi32((int)sha256_h[2]));
    D = _mm_add_epi32(D, _mm_set1_epi32((int)sha256_h[3]));
    E = _mm_add_epi32(E, _mm_set1_epi32((int)sha256_h[4]));
    F = _mm_add_epi32(F, _mm_set1_epi32((int)sha256_h[5]));
    G = _mm_add_epi32(G, _mm_set1_epi32((int)sha256_h[6]));
    H = _mm_add_epi32(H, _mm_set1_epi32((int)sha256_h[7]));

    uint32_t tmpv[4];
    _mm_storeu_si128((__m128i*)tmpv, A); for (int lane=0; lane<4; lane++) hash[0*4+lane]=tmpv[lane];
    _mm_storeu_si128((__m128i*)tmpv, B); for (int lane=0; lane<4; lane++) hash[1*4+lane]=tmpv[lane];
    _mm_storeu_si128((__m128i*)tmpv, C); for (int lane=0; lane<4; lane++) hash[2*4+lane]=tmpv[lane];
    _mm_storeu_si128((__m128i*)tmpv, D); for (int lane=0; lane<4; lane++) hash[3*4+lane]=tmpv[lane];
    _mm_storeu_si128((__m128i*)tmpv, E); for (int lane=0; lane<4; lane++) hash[4*4+lane]=tmpv[lane];
    _mm_storeu_si128((__m128i*)tmpv, F); for (int lane=0; lane<4; lane++) hash[5*4+lane]=tmpv[lane];
    _mm_storeu_si128((__m128i*)tmpv, G); for (int lane=0; lane<4; lane++) hash[6*4+lane]=tmpv[lane];
    _mm_storeu_si128((__m128i*)tmpv, H); for (int lane=0; lane<4; lane++) hash[7*4+lane]=tmpv[lane];
}

/* 4-way AVX variant: same logic, compiled with AVX target to enable VEX encoding */
#if defined(__GNUC__)
__attribute__((target("avx")))
#endif
static void sha256d_ms_4way_avx(uint32_t *hash, uint32_t *data,
    const uint32_t *midstate, const uint32_t *prehash)
{
    sha256d_ms_4way_simd(hash, data, midstate, prehash);
}

static inline int scanhash_sha256d_4way(int thr_id, uint32_t *pdata,
    const uint32_t *ptarget, uint32_t max_nonce, unsigned long *hashes_done)
{
    uint32_t data[4 * 64] __attribute__((aligned(128)));
    uint32_t hash[4 * 8] __attribute__((aligned(32)));
    uint32_t midstate[4 * 8] __attribute__((aligned(32)));
    uint32_t prehash[4 * 8] __attribute__((aligned(32)));
    uint32_t n = pdata[19] - 1;
    const uint32_t first_nonce = pdata[19];
    const uint32_t Htarg = ptarget[7];
    int i, j;

    uint32_t block2[16];
    /* Build big-endian view of header words for midstate and block2 */
    uint32_t pdata_be[20];
    for (i = 0; i < 20; ++i) pdata_be[i] = swab32(pdata[i]);
    cpunet_build_block2(block2, pdata_be);
    for (i = 0; i < 16; i++)
        for (j = 0; j < 4; j++)
            data[i * 4 + j] = block2[i];

    sha256_init(midstate);
    /* Use big-endian word view for SHA256 midstate */
    sha256_transform(midstate, pdata_be, 0);
    memcpy(prehash, midstate, 32);
    sha256d_prehash(prehash, block2);
    for (i = 7; i >= 0; i--) {
        for (j = 0; j < 4; j++) {
            midstate[i * 4 + j] = midstate[i];
            prehash[i * 4 + j] = prehash[i];
        }
    }
    uint32_t midstate_one[8], prehash_one[8];
    memcpy(midstate_one, midstate, 32);
    memcpy(prehash_one, prehash, 32);

    do {
        /* normal vector path */
        for (i = 0; i < 4; i++)
            data[4 * 3 + i] = swab32(++n);

        /* Use 4-way AVX kernel if AVX is available, else SSE2 */
        if (
#if defined(__x86_64__)
            cpu_has_avx()
#else
            0
#endif
           )
            sha256d_ms_4way_avx(hash, data, midstate, prehash);
        else
            sha256d_ms_4way_simd(hash, data, midstate, prehash);

        /* Report only the best lane for diagnostics to reduce overhead. */
        int best_lane = 0;
        for (i = 1; i < 4; i++) {
            if (words_leq_256(&hash[4 * i], &hash[4 * best_lane]))
                best_lane = i;
        }
        miner_report_candidate(thr_id, pdata, swab32(data[4 * 3 + best_lane]), swab32(hash[4 * 7 + best_lane]));

        for (i = 0; i < 4; i++) {
            uint32_t lane_nonce = swab32(data[4 * 3 + i]);
            if (lane_nonce > max_nonce)
                continue; /* respect max_nonce bound for final batch */
            if (swab32(hash[4 * 7 + i]) <= Htarg) {
                if (opt_debug) {
                    printf("\nDEBUG: 4-way scan path found potential solution (lane %d)!\n", i);
                    printf("Scan path hash[%d][7]: %08x (swab32: %08x)\n", i, hash[4 * 7 + i], swab32(hash[4 * 7 + i]));
                    printf("Target Htarg:          %08x\n", Htarg);
                }

                pdata[19] = lane_nonce;
                if (opt_debug) {
                    if (cpunet_validate_and_print(i, pdata, lane_nonce, ptarget)) {
                        *hashes_done = n - first_nonce + 1;
                        return 1;
                    }
                } else {
                    uint32_t canon2[8];
                    for (int j3 = 0; j3 < 8; j3++) canon2[j3] = swab32(hash[4 * j3 + i]);
                    if (fulltest(canon2, ptarget)) {
                        *hashes_done = n - first_nonce + 1;
                        return 1;
                    }
                }
            }
        }
    } while (n < max_nonce && !work_restart[thr_id].restart);

    *hashes_done = n - first_nonce + 1;
    pdata[19] = n;
    return 0;
}

#endif /* HAVE_SHA256_4WAY */

#ifdef HAVE_SHA256_8WAY

void sha256d_ms_8way(uint32_t *hash,  uint32_t *data,
    const uint32_t *midstate, const uint32_t *prehash);

/* Correctness-first C reference for 8-way: derive each lane from scalar path. */
static inline void sha256d_ms_8way_c(uint32_t *hash, uint32_t *data,
    const uint32_t *midstate, const uint32_t *prehash)
{
    for (int lane = 0; lane < 8; lane++) {
        uint32_t W[64];
        for (int i = 0; i < 16; i++) W[i] = data[i * 8 + lane];
        sha256d_preextend(W);
        uint32_t ms[8], ph[8], out[8];
        for (int i = 0; i < 8; i++) {
            ms[i] = midstate[i * 8 + lane];
            ph[i] = prehash[i * 8 + lane];
        }
        sha256d_ms(out, W, ms, ph);
        for (int i = 0; i < 8; i++) hash[i * 8 + lane] = out[i];
    }
}

/* AVX2 helpers at file scope to avoid nested function definitions */
#if defined(__x86_64__)
#if defined(__GNUC__)
__attribute__((target("avx2")))
#endif
static inline __m256i avx2_ror32(__m256i x, int n) {
    return _mm256_or_si256(_mm256_srli_epi32(x, n), _mm256_slli_epi32(x, 32 - n));
}
#if defined(__GNUC__)
__attribute__((target("avx2")))
#endif
static inline __m256i avx2_S0(__m256i x) {
    return _mm256_xor_si256(_mm256_xor_si256(avx2_ror32(x,2), avx2_ror32(x,13)), avx2_ror32(x,22));
}
#if defined(__GNUC__)
__attribute__((target("avx2")))
#endif
static inline __m256i avx2_S1(__m256i x) {
    return _mm256_xor_si256(_mm256_xor_si256(avx2_ror32(x,6), avx2_ror32(x,11)), avx2_ror32(x,25));
}
#if defined(__GNUC__)
__attribute__((target("avx2")))
#endif
static inline __m256i avx2_s0(__m256i x) {
    return _mm256_xor_si256(_mm256_xor_si256(avx2_ror32(x,7), avx2_ror32(x,18)), _mm256_srli_epi32(x,3));
}
#if defined(__GNUC__)
__attribute__((target("avx2")))
#endif
static inline __m256i avx2_s1(__m256i x) {
    return _mm256_xor_si256(_mm256_xor_si256(avx2_ror32(x,17), avx2_ror32(x,19)), _mm256_srli_epi32(x,10));
}

#if defined(__GNUC__)
__attribute__((target("avx2")))
#endif
static void sha256d_ms_8way_simd(uint32_t *hash, uint32_t *data,
    const uint32_t *midstate, const uint32_t *prehash)
{
    static __m256i K8[64];
    static int K8_init = 0;
    if (!K8_init) {
        for (int i = 0; i < 64; i++) K8[i] = _mm256_set1_epi32((int)sha256_k[i]);
        K8_init = 1;
    }
    __m256i W[16];
    const __m256i *d8 = (const __m256i *) __builtin_assume_aligned(data, 32);
    for (int i = 0; i < 16; i++)
        W[i] = _mm256_load_si256(d8 + i);
    __m256i A = _mm256_set_epi32((int)midstate[0*8+7],(int)midstate[0*8+6],(int)midstate[0*8+5],(int)midstate[0*8+4],(int)midstate[0*8+3],(int)midstate[0*8+2],(int)midstate[0*8+1],(int)midstate[0*8+0]);
    __m256i B = _mm256_set_epi32((int)midstate[1*8+7],(int)midstate[1*8+6],(int)midstate[1*8+5],(int)midstate[1*8+4],(int)midstate[1*8+3],(int)midstate[1*8+2],(int)midstate[1*8+1],(int)midstate[1*8+0]);
    __m256i C = _mm256_set_epi32((int)midstate[2*8+7],(int)midstate[2*8+6],(int)midstate[2*8+5],(int)midstate[2*8+4],(int)midstate[2*8+3],(int)midstate[2*8+2],(int)midstate[2*8+1],(int)midstate[2*8+0]);
    __m256i D = _mm256_set_epi32((int)midstate[3*8+7],(int)midstate[3*8+6],(int)midstate[3*8+5],(int)midstate[3*8+4],(int)midstate[3*8+3],(int)midstate[3*8+2],(int)midstate[3*8+1],(int)midstate[3*8+0]);
    __m256i E = _mm256_set_epi32((int)midstate[4*8+7],(int)midstate[4*8+6],(int)midstate[4*8+5],(int)midstate[4*8+4],(int)midstate[4*8+3],(int)midstate[4*8+2],(int)midstate[4*8+1],(int)midstate[4*8+0]);
    __m256i F = _mm256_set_epi32((int)midstate[5*8+7],(int)midstate[5*8+6],(int)midstate[5*8+5],(int)midstate[5*8+4],(int)midstate[5*8+3],(int)midstate[5*8+2],(int)midstate[5*8+1],(int)midstate[5*8+0]);
    __m256i G = _mm256_set_epi32((int)midstate[6*8+7],(int)midstate[6*8+6],(int)midstate[6*8+5],(int)midstate[6*8+4],(int)midstate[6*8+3],(int)midstate[6*8+2],(int)midstate[6*8+1],(int)midstate[6*8+0]);
    __m256i H = _mm256_set_epi32((int)midstate[7*8+7],(int)midstate[7*8+6],(int)midstate[7*8+5],(int)midstate[7*8+4],(int)midstate[7*8+3],(int)midstate[7*8+2],(int)midstate[7*8+1],(int)midstate[7*8+0]);
    __m256i SA=A,SB=B,SC=C,SD=D,SE=E,SF=F,SG=G,SH=H;
    #if defined(__GNUC__)
    #pragma GCC unroll 8
    #endif
    for (int i=0;i<64;i++){
        int t = i & 15;
        if (i >= 16) {
            __m256i wim2 = W[(t + 14) & 15];
            __m256i wim7 = W[(t + 9) & 15];
            __m256i wim15 = W[(t + 1) & 15];
            __m256i wim16 = W[t];
            W[t] = _mm256_add_epi32(_mm256_add_epi32(avx2_s1(wim2), wim7), _mm256_add_epi32(avx2_s0(wim15), wim16));
        }
        const __m256i Ki = K8[i];
        __m256i ch = _mm256_xor_si256(_mm256_and_si256(E,F), _mm256_andnot_si256(E,G));
        __m256i t1 = _mm256_add_epi32(H, _mm256_add_epi32(_mm256_add_epi32(Ki, W[t]), _mm256_add_epi32(ch, avx2_S1(E))));
        __m256i maj = _mm256_xor_si256(_mm256_xor_si256(_mm256_and_si256(A,B), _mm256_and_si256(A,C)), _mm256_and_si256(B,C));
        __m256i t2 = _mm256_add_epi32(maj, avx2_S0(A));
        D = _mm256_add_epi32(D, t1);
        H = _mm256_add_epi32(t1, t2);
        __m256i tmp=H; H=G; G=F; F=E; E=D; D=C; C=B; B=A; A=tmp;
    }
    A=_mm256_add_epi32(A,SA);B=_mm256_add_epi32(B,SB);C=_mm256_add_epi32(C,SC);D=_mm256_add_epi32(D,SD);
    E=_mm256_add_epi32(E,SE);F=_mm256_add_epi32(F,SF);G=_mm256_add_epi32(G,SG);H=_mm256_add_epi32(H,SH);
    __m256i W2v[16];
    W2v[0]=A;W2v[1]=B;W2v[2]=C;W2v[3]=D;W2v[4]=E;W2v[5]=F;W2v[6]=G;W2v[7]=H;
    for (int i=8;i<16;i++) W2v[i]=_mm256_set1_epi32((int)sha256d_hash1[i]);
    A=_mm256_set1_epi32((int)sha256_h[0]);B=_mm256_set1_epi32((int)sha256_h[1]);
    C=_mm256_set1_epi32((int)sha256_h[2]);D=_mm256_set1_epi32((int)sha256_h[3]);
    E=_mm256_set1_epi32((int)sha256_h[4]);F=_mm256_set1_epi32((int)sha256_h[5]);
    G=_mm256_set1_epi32((int)sha256_h[6]);H=_mm256_set1_epi32((int)sha256_h[7]);
    static __m256i P2_17_8, P2_23_8, P2_24_8, P2_30_8; static int P2_8_init=0; static int use_preext2_8=1;
    if (!P2_8_init) { P2_17_8=_mm256_set1_epi32(0x00a00000); P2_23_8=_mm256_set1_epi32(0x11002000); P2_24_8=_mm256_set1_epi32(0x80000000); P2_30_8=_mm256_set1_epi32(0x00400022); P2_8_init=1; }
    /* JIT schedule: do not precompute W2[16..31]; extend on-demand per round */
    int primed_count = 16;
    /* 4-round unrolled second pass with inline fold-ins at i+offset */
    #define AVX2_ROUND2(AA,BB,CC,DD,EE,FF,GG,HH, WT, KI) do { \
        __m256i ch_ = _mm256_xor_si256(_mm256_and_si256((EE),(FF)), _mm256_andnot_si256((EE),(GG))); \
        __m256i t1_ = _mm256_add_epi32((HH), _mm256_add_epi32(avx2_S1(EE), _mm256_add_epi32(ch_, _mm256_add_epi32((WT),(KI))))); \
        __m256i maj_ = _mm256_xor_si256(_mm256_xor_si256(_mm256_and_si256((AA),(BB)), _mm256_and_si256((AA),(CC))), _mm256_and_si256((BB),(CC))); \
        __m256i t2_ = _mm256_add_epi32(avx2_S0(AA), maj_); \
        (DD) = _mm256_add_epi32((DD), t1_); \
        (HH) = _mm256_add_epi32(t1_, t2_); \
        __m256i tmp_ = (HH); (HH) = (GG); (GG) = (FF); (FF) = (EE); (EE) = (DD); (DD) = (CC); (CC) = (BB); (BB) = (AA); (AA) = tmp_; \
    } while(0)

    for (int i = 0; i < 64; i += 4) {
        int t0 = (i + 0) & 15; int t1i = (i + 1) & 15; int t2i = (i + 2) & 15; int t3 = (i + 3) & 15;
        if (i >= 16) {
            __m256i w0_i2 = W2v[(t0 + 14) & 15];
            __m256i w0_i7 = W2v[(t0 + 9) & 15];
            __m256i w0_i15= W2v[(t0 + 1) & 15];
            __m256i w0_i16= W2v[t0];
            __m256i w0 = _mm256_add_epi32(_mm256_add_epi32(avx2_s1(w0_i2), w0_i7), _mm256_add_epi32(avx2_s0(w0_i15), w0_i16));
            if (use_preext2_8 && (i + 0) < 32) { if (i + 0 == 17) w0 = _mm256_add_epi32(w0, P2_17_8); }
            W2v[t0] = w0;

            __m256i w1_i2 = W2v[(t1i + 14) & 15];
            __m256i w1_i7 = W2v[(t1i + 9) & 15];
            __m256i w1_i15= W2v[(t1i + 1) & 15];
            __m256i w1_i16= W2v[t1i];
            __m256i w1 = _mm256_add_epi32(_mm256_add_epi32(avx2_s1(w1_i2), w1_i7), _mm256_add_epi32(avx2_s0(w1_i15), w1_i16));
            if (use_preext2_8 && (i + 1) < 32) { if (i + 1 == 23) w1 = _mm256_add_epi32(w1, P2_23_8); }
            W2v[t1i] = w1;

            __m256i w2_i2 = W2v[(t2i + 14) & 15];
            __m256i w2_i7 = W2v[(t2i + 9) & 15];
            __m256i w2_i15= W2v[(t2i + 1) & 15];
            __m256i w2_i16= W2v[t2i];
            __m256i w2 = _mm256_add_epi32(_mm256_add_epi32(avx2_s1(w2_i2), w2_i7), _mm256_add_epi32(avx2_s0(w2_i15), w2_i16));
            if (use_preext2_8 && (i + 2) < 32) { if (i + 2 == 24) w2 = _mm256_add_epi32(w2, P2_24_8); }
            W2v[t2i] = w2;

            __m256i w3_i2 = W2v[(t3 + 14) & 15];
            __m256i w3_i7 = W2v[(t3 + 9) & 15];
            __m256i w3_i15= W2v[(t3 + 1) & 15];
            __m256i w3_i16= W2v[t3];
            __m256i w3 = _mm256_add_epi32(_mm256_add_epi32(avx2_s1(w3_i2), w3_i7), _mm256_add_epi32(avx2_s0(w3_i15), w3_i16));
            if (use_preext2_8 && (i + 3) < 32) { if (i + 3 == 30) w3 = _mm256_add_epi32(w3, P2_30_8); }
            W2v[t3] = w3;
        }
        if (opt_debug && i >= 16 && i < 32) {
            applog(LOG_DEBUG, "DBG 8way second-pass map: i=%d t=%d preext=%d", i+0, t0, use_preext2_8);
            applog(LOG_DEBUG, "DBG 8way second-pass map: i=%d t=%d preext=%d", i+1, t1i, use_preext2_8);
            applog(LOG_DEBUG, "DBG 8way second-pass map: i=%d t=%d preext=%d", i+2, t2i, use_preext2_8);
            applog(LOG_DEBUG, "DBG 8way second-pass map: i=%d t=%d preext=%d", i+3, t3, use_preext2_8);
        }
        AVX2_ROUND2(A,B,C,D,E,F,G,H, W2v[t0], K8[i+0]);
        AVX2_ROUND2(A,B,C,D,E,F,G,H, W2v[t1i], K8[i+1]);
        AVX2_ROUND2(A,B,C,D,E,F,G,H, W2v[t2i], K8[i+2]);
        AVX2_ROUND2(A,B,C,D,E,F,G,H, W2v[t3], K8[i+3]);
    }
    #undef AVX2_ROUND2
    A=_mm256_add_epi32(A,_mm256_set1_epi32((int)sha256_h[0]));
    B=_mm256_add_epi32(B,_mm256_set1_epi32((int)sha256_h[1]));
    C=_mm256_add_epi32(C,_mm256_set1_epi32((int)sha256_h[2]));
    D=_mm256_add_epi32(D,_mm256_set1_epi32((int)sha256_h[3]));
    E=_mm256_add_epi32(E,_mm256_set1_epi32((int)sha256_h[4]));
    F=_mm256_add_epi32(F,_mm256_set1_epi32((int)sha256_h[5]));
    G=_mm256_add_epi32(G,_mm256_set1_epi32((int)sha256_h[6]));
    H=_mm256_add_epi32(H,_mm256_set1_epi32((int)sha256_h[7]));
    uint32_t v8[8];
    _mm256_storeu_si256((__m256i*)v8, A); for (int lane=0; lane<8; lane++) hash[0*8+lane]=v8[lane];
    _mm256_storeu_si256((__m256i*)v8, B); for (int lane=0; lane<8; lane++) hash[1*8+lane]=v8[lane];
    _mm256_storeu_si256((__m256i*)v8, C); for (int lane=0; lane<8; lane++) hash[2*8+lane]=v8[lane];
    _mm256_storeu_si256((__m256i*)v8, D); for (int lane=0; lane<8; lane++) hash[3*8+lane]=v8[lane];
    _mm256_storeu_si256((__m256i*)v8, E); for (int lane=0; lane<8; lane++) hash[4*8+lane]=v8[lane];
    _mm256_storeu_si256((__m256i*)v8, F); for (int lane=0; lane<8; lane++) hash[5*8+lane]=v8[lane];
    _mm256_storeu_si256((__m256i*)v8, G); for (int lane=0; lane<8; lane++) hash[6*8+lane]=v8[lane];
    _mm256_storeu_si256((__m256i*)v8, H); for (int lane=0; lane<8; lane++) hash[7*8+lane]=v8[lane];
}
#endif

static inline int scanhash_sha256d_8way(int thr_id, uint32_t *pdata,
    const uint32_t *ptarget, uint32_t max_nonce, unsigned long *hashes_done)
{
    uint32_t data[8 * 64] __attribute__((aligned(128)));
    uint32_t hash[8 * 8] __attribute__((aligned(32)));
    uint32_t midstate[8 * 8] __attribute__((aligned(32)));
    uint32_t prehash[8 * 8] __attribute__((aligned(32)));
    uint32_t n = pdata[19] - 1;
    const uint32_t first_nonce = pdata[19];
    const uint32_t Htarg = ptarget[7];
    int i, j;

    uint32_t block2[16];
    /* Build big-endian view of header words for midstate and block2 */
    uint32_t pdata_be[20];
    for (i = 0; i < 20; ++i) pdata_be[i] = swab32(pdata[i]);
    cpunet_build_block2(block2, pdata_be);
    for (i = 0; i < 16; i++)
        for (j = 0; j < 8; j++)
            data[i * 8 + j] = block2[i];

    uint32_t temp_midstate[8], temp_prehash[8];
    sha256_init(temp_midstate);
    /* Use big-endian word view for SHA256 midstate */
    sha256_transform(temp_midstate, pdata_be, 0);
    memcpy(temp_prehash, temp_midstate, 32);
    sha256d_prehash(temp_prehash, block2);
    for (i = 0; i < 8; i++) {
        for (j = 0; j < 8; j++) {
            midstate[i * 8 + j] = temp_midstate[i];
            prehash[i * 8 + j] = temp_prehash[i];
        }
    }
    /* Also single-lane copies for self-check branch */
    uint32_t midstate_one8[8], prehash_one8[8];
    memcpy(midstate_one8, temp_midstate, 32);
    memcpy(prehash_one8, temp_prehash, 32);

    do {
        for (i = 0; i < 8; i++)
            data[8 * 3 + i] = swab32(++n);

        /* Use 8-way SIMD kernel when available, else fallback C */
        if (sha256_use_8way())
            sha256d_ms_8way_simd(hash, data, midstate, prehash);
        else
            sha256d_ms_8way_c(hash, data, midstate, prehash);

        /* Debug: bypass precheck by fulltest on all lanes when enabled */
        if (opt_debug_lax_target || opt_debug_sample_canonical) {
            for (i = 0; i < 8; i++) {
                uint32_t ln = swab32(data[8 * 3 + i]);
                if (ln > max_nonce)
                    continue; /* respect bound during self-check and tests */
                uint32_t canon[8];
                for (int j2 = 0; j2 < 8; j2++) canon[j2] = swab32(hash[8 * j2 + i]);
                if (fulltest(canon, ptarget)) {
                    pdata[19] = ln;
                    *hashes_done = n - first_nonce + 1;
                    return 1;
                }
            }
        }

        /* Report only the best lane for diagnostics to reduce overhead. */
        int best_lane = 0;
        for (i = 1; i < 8; i++) {
            if (words_leq_256(&hash[8 * i], &hash[8 * best_lane]))
                best_lane = i;
        }
        miner_report_candidate(thr_id, pdata, swab32(data[8 * 3 + best_lane]), swab32(hash[8 * 7 + best_lane]));

        for (i = 0; i < 8; i++) {
            uint32_t ln = swab32(data[8 * 3 + i]);
            if (ln > max_nonce)
                continue; /* do not accept lanes beyond max_nonce */
            if (swab32(hash[8 * 7 + i]) <= Htarg) {
                if (opt_debug) {
                    printf("\nDEBUG: 8-way precheck hit (lane %d)\n", i);
                    printf("Precheck top word:   %08x (be: %08x)\n", hash[8 * 7 + i], swab32(hash[8 * 7 + i]));
                    printf("Target Htarg:        %08x\n", Htarg);
                }

                pdata[19] = ln;
                if (opt_debug) {
                    if (cpunet_validate_and_print(i, pdata, ln, ptarget)) {
                        *hashes_done = n - first_nonce + 1;
                        return 1;
                    }
                } else {
                    uint32_t canon2[8];
                    for (int j3 = 0; j3 < 8; j3++) canon2[j3] = swab32(hash[8 * j3 + i]);
                    if (fulltest(canon2, ptarget)) {
                        *hashes_done = n - first_nonce + 1;
                        return 1;
                    }
                }
            }
        }
    } while (n < max_nonce && !work_restart[thr_id].restart);

    *hashes_done = n - first_nonce + 1;
    pdata[19] = n;
    return 0;
}

#endif /* HAVE_SHA256_8WAY */

#if defined(__x86_64__)
/* AVX-512 helpers (intrinsics; independent of external assembly files) */
#if defined(__GNUC__)
__attribute__((target("avx512f")))
#endif
static inline __m512i avx512_pack512(const uint32_t *lo, const uint32_t *hi)
{
    const __m256i *lo_al = (const __m256i *) __builtin_assume_aligned(lo, 32);
    const __m256i *hi_al = (const __m256i *) __builtin_assume_aligned(hi, 32);
    __m256i lo256 = _mm256_load_si256(lo_al);
    __m256i hi256 = _mm256_load_si256(hi_al);
    __m512i v = _mm512_castsi256_si512(lo256);
    return _mm512_inserti64x4(v, hi256, 1);
}

#if defined(__GNUC__)
__attribute__((target("avx512f")))
#endif
static inline __m512i avx512_ror32(__m512i x, int n)
{
    __m512i a = _mm512_srli_epi32(x, n);
    __m512i b = _mm512_slli_epi32(x, 32 - n);
    return _mm512_or_si512(a, b);
}

#if defined(__GNUC__)
__attribute__((target("avx512f")))
#endif
static inline __m512i avx512_S0(__m512i x)
{
    return _mm512_xor_si512(_mm512_xor_si512(avx512_ror32(x,2), avx512_ror32(x,13)), avx512_ror32(x,22));
}

#if defined(__GNUC__)
__attribute__((target("avx512f")))
#endif
static inline __m512i avx512_S1(__m512i x)
{
    return _mm512_xor_si512(_mm512_xor_si512(avx512_ror32(x,6), avx512_ror32(x,11)), avx512_ror32(x,25));
}

#if defined(__GNUC__)
__attribute__((target("avx512f")))
#endif
static inline __m512i avx512_s0(__m512i x)
{
    return _mm512_xor_si512(_mm512_xor_si512(avx512_ror32(x,7), avx512_ror32(x,18)), _mm512_srli_epi32(x,3));
}

#if defined(__GNUC__)
__attribute__((target("avx512f")))
#endif
static inline __m512i avx512_s1(__m512i x)
{
    return _mm512_xor_si512(_mm512_xor_si512(avx512_ror32(x,17), avx512_ror32(x,19)), _mm512_srli_epi32(x,10));
}

#if defined(__GNUC__)
__attribute__((target("avx512f")))
#endif
static void sha256d_ms_16way_avx512(uint32_t *hA, uint32_t *hB,
    const uint32_t *dA, const uint32_t *dB,
    const uint32_t *mA, const uint32_t *pA,
    const uint32_t *mB, const uint32_t *pB)
{
    /* Pre-broadcast K constants */
    static __m512i K16[64];
    static int K16_init = 0;
    if (!K16_init) { for (int i=0;i<64;i++) K16[i]=_mm512_set1_epi32((int)sha256_k[i]); K16_init=1; }
    /* Use midstate as initial A..H and run full 64 rounds on block2 with rolling W */
    __m512i W[16];
    for (int i = 0; i < 16; i++)
        W[i] = avx512_pack512(dA + 8*i, dB + 8*i);
    __m512i A = avx512_pack512(mA + 8*0, mB + 8*0);
    __m512i B = avx512_pack512(mA + 8*1, mB + 8*1);
    __m512i C = avx512_pack512(mA + 8*2, mB + 8*2);
    __m512i D = avx512_pack512(mA + 8*3, mB + 8*3);
    __m512i E = avx512_pack512(mA + 8*4, mB + 8*4);
    __m512i F = avx512_pack512(mA + 8*5, mB + 8*5);
    __m512i G = avx512_pack512(mA + 8*6, mB + 8*6);
    __m512i H = avx512_pack512(mA + 8*7, mB + 8*7);
    __m512i SA = A, SB = B, SC = C, SD = D, SE = E, SF = F, SG = G, SH = H;
    #if defined(__GNUC__)
    #pragma GCC unroll 8
    #endif
    #define AVX512_ROUND(AA,BB,CC,DD,EE,FF,GG,HH, WT, KI) do { \
        __m512i t1 = _mm512_add_epi32((HH), _mm512_add_epi32(avx512_S1(EE), \
            _mm512_add_epi32(_mm512_xor_si512(_mm512_and_si512((EE),(FF)), _mm512_andnot_si512((EE),(GG))), \
                              _mm512_add_epi32((WT), (KI))))); \
        __m512i t2 = _mm512_add_epi32(avx512_S0(AA), _mm512_xor_si512(_mm512_xor_si512(_mm512_and_si512((AA),(BB)), _mm512_and_si512((AA),(CC))), _mm512_and_si512((BB),(CC)))); \
        (DD) = _mm512_add_epi32((DD), t1); \
        (HH) = _mm512_add_epi32(t1, t2); \
        __m512i tmp_ = (HH); (HH)=(GG); (GG)=(FF); (FF)=(EE); (EE)=(DD); (DD)=(CC); (CC)=(BB); (BB)=(AA); (AA)=tmp_; \
    } while(0)

    for (int i = 0; i < 64; i+=4) {
        int t0=(i+0)&15, t1i=(i+1)&15, t2i=(i+2)&15, t3=(i+3)&15;
        if (i >= 16) {
            W[t0] = _mm512_add_epi32(_mm512_add_epi32(avx512_s1(W[(t0+14)&15]), W[(t0+9)&15]), _mm512_add_epi32(avx512_s0(W[(t0+1)&15]), W[t0]));
            W[t1i] = _mm512_add_epi32(_mm512_add_epi32(avx512_s1(W[(t1i+14)&15]), W[(t1i+9)&15]), _mm512_add_epi32(avx512_s0(W[(t1i+1)&15]), W[t1i]));
            W[t2i] = _mm512_add_epi32(_mm512_add_epi32(avx512_s1(W[(t2i+14)&15]), W[(t2i+9)&15]), _mm512_add_epi32(avx512_s0(W[(t2i+1)&15]), W[t2i]));
            W[t3] = _mm512_add_epi32(_mm512_add_epi32(avx512_s1(W[(t3+14)&15]), W[(t3+9)&15]), _mm512_add_epi32(avx512_s0(W[(t3+1)&15]), W[t3]));
        }
        AVX512_ROUND(A,B,C,D,E,F,G,H, W[t0], K16[i+0]);
        AVX512_ROUND(A,B,C,D,E,F,G,H, W[t1i], K16[i+1]);
        AVX512_ROUND(A,B,C,D,E,F,G,H, W[t2i], K16[i+2]);
        AVX512_ROUND(A,B,C,D,E,F,G,H, W[t3], K16[i+3]);
    }
    #undef AVX512_ROUND
    /* Feed-forward: add starting prehash state to produce first-pass digest words */
    A = _mm512_add_epi32(A, SA);
    B = _mm512_add_epi32(B, SB);
    C = _mm512_add_epi32(C, SC);
    D = _mm512_add_epi32(D, SD);
    E = _mm512_add_epi32(E, SE);
    F = _mm512_add_epi32(F, SF);
    G = _mm512_add_epi32(G, SG);
    H = _mm512_add_epi32(H, SH);

    __m512i stA = A, stBv = B, stCv = C, stDv = D, stEv = E, stFv = F, stGv = G, stHv = H;
    __m512i W2[16];
    static __m512i P2_17_16, P2_23_16, P2_24_16, P2_30_16; static int P2_16_init=0; static int use_preext2_16=1;
    if (!P2_16_init) { P2_17_16=_mm512_set1_epi32(0x00a00000); P2_23_16=_mm512_set1_epi32(0x11002000); P2_24_16=_mm512_set1_epi32(0x80000000); P2_30_16=_mm512_set1_epi32(0x00400022); P2_16_init=1; }
    W2[0] = stA; W2[1] = stBv; W2[2] = stCv; W2[3] = stDv;
    W2[4] = stEv; W2[5] = stFv; W2[6] = stGv; W2[7] = stHv;
    for (int i = 8; i < 16; i++) W2[i] = _mm512_set1_epi32((int)sha256d_hash1[i]);

    A = _mm512_set1_epi32((int)sha256_h[0]);
    B = _mm512_set1_epi32((int)sha256_h[1]);
    C = _mm512_set1_epi32((int)sha256_h[2]);
    D = _mm512_set1_epi32((int)sha256_h[3]);
    E = _mm512_set1_epi32((int)sha256_h[4]);
    F = _mm512_set1_epi32((int)sha256_h[5]);
    G = _mm512_set1_epi32((int)sha256_h[6]);
    H = _mm512_set1_epi32((int)sha256_h[7]);
    #if defined(__GNUC__)
    #pragma GCC unroll 8
    #endif
    #define AVX512_ROUND2(AA,BB,CC,DD,EE,FF,GG,HH, WT, KI) do { \
        __m512i t1 = _mm512_add_epi32((HH), _mm512_add_epi32(avx512_S1(EE), \
            _mm512_add_epi32(_mm512_xor_si512(_mm512_and_si512((EE),(FF)), _mm512_andnot_si512((EE),(GG))), \
                              _mm512_add_epi32((WT), (KI))))); \
        __m512i t2 = _mm512_add_epi32(avx512_S0(AA), _mm512_xor_si512(_mm512_xor_si512(_mm512_and_si512((AA),(BB)), _mm512_and_si512((AA),(CC))), _mm512_and_si512((BB),(CC)))); \
        (DD) = _mm512_add_epi32((DD), t1); \
        (HH) = _mm512_add_epi32(t1, t2); \
        __m512i tmp_ = (HH); (HH)=(GG); (GG)=(FF); (FF)=(EE); (EE)=(DD); (DD)=(CC); (CC)=(BB); (BB)=(AA); (AA)=tmp_; \
    } while(0)

    for (int i = 0; i < 64; i+=4) {
        int t0=(i+0)&15, t1i=(i+1)&15, t2i=(i+2)&15, t3=(i+3)&15;
        if (i >= 16) {
            W2[t0] = _mm512_add_epi32(_mm512_add_epi32(avx512_s1(W2[(t0+14)&15]), W2[(t0+9)&15]), _mm512_add_epi32(avx512_s0(W2[(t0+1)&15]), W2[t0])); if (use_preext2_16 && i+0==17) W2[t0]=_mm512_add_epi32(W2[t0], P2_17_16);
            W2[t1i] = _mm512_add_epi32(_mm512_add_epi32(avx512_s1(W2[(t1i+14)&15]), W2[(t1i+9)&15]), _mm512_add_epi32(avx512_s0(W2[(t1i+1)&15]), W2[t1i])); if (use_preext2_16 && i+1==23) W2[t1i]=_mm512_add_epi32(W2[t1i], P2_23_16);
            W2[t2i] = _mm512_add_epi32(_mm512_add_epi32(avx512_s1(W2[(t2i+14)&15]), W2[(t2i+9)&15]), _mm512_add_epi32(avx512_s0(W2[(t2i+1)&15]), W2[t2i])); if (use_preext2_16 && i+2==24) W2[t2i]=_mm512_add_epi32(W2[t2i], P2_24_16);
            W2[t3] = _mm512_add_epi32(_mm512_add_epi32(avx512_s1(W2[(t3+14)&15]), W2[(t3+9)&15]), _mm512_add_epi32(avx512_s0(W2[(t3+1)&15]), W2[t3])); if (use_preext2_16 && i+3==30) W2[t3]=_mm512_add_epi32(W2[t3], P2_30_16);
        }
        AVX512_ROUND2(A,B,C,D,E,F,G,H, W2[t0], K16[i+0]);
        AVX512_ROUND2(A,B,C,D,E,F,G,H, W2[t1i], K16[i+1]);
        AVX512_ROUND2(A,B,C,D,E,F,G,H, W2[t2i], K16[i+2]);
        AVX512_ROUND2(A,B,C,D,E,F,G,H, W2[t3], K16[i+3]);
    }
    #undef AVX512_ROUND2
    A = _mm512_add_epi32(A, _mm512_set1_epi32((int)sha256_h[0]));
    B = _mm512_add_epi32(B, _mm512_set1_epi32((int)sha256_h[1]));
    C = _mm512_add_epi32(C, _mm512_set1_epi32((int)sha256_h[2]));
    D = _mm512_add_epi32(D, _mm512_set1_epi32((int)sha256_h[3]));
    E = _mm512_add_epi32(E, _mm512_set1_epi32((int)sha256_h[4]));
    F = _mm512_add_epi32(F, _mm512_set1_epi32((int)sha256_h[5]));
    G = _mm512_add_epi32(G, _mm512_set1_epi32((int)sha256_h[6]));
    H = _mm512_add_epi32(H, _mm512_set1_epi32((int)sha256_h[7]));

    __m256i a_lo = _mm512_castsi512_si256(A), a_hi = _mm512_extracti64x4_epi64(A, 1);
    __m256i b_lo = _mm512_castsi512_si256(B), b_hi = _mm512_extracti64x4_epi64(B, 1);
    __m256i c_lo = _mm512_castsi512_si256(C), c_hi = _mm512_extracti64x4_epi64(C, 1);
    __m256i d_lo = _mm512_castsi512_si256(D), d_hi = _mm512_extracti64x4_epi64(D, 1);
    __m256i e_lo = _mm512_castsi512_si256(E), e_hi = _mm512_extracti64x4_epi64(E, 1);
    __m256i f_lo = _mm512_castsi512_si256(F), f_hi = _mm512_extracti64x4_epi64(F, 1);
    __m256i g_lo = _mm512_castsi512_si256(G), g_hi = _mm512_extracti64x4_epi64(G, 1);
    __m256i h_lo = _mm512_castsi512_si256(H), h_hi = _mm512_extracti64x4_epi64(H, 1);

    _mm256_storeu_si256((__m256i *)(hA + 8*0), a_lo);
    _mm256_storeu_si256((__m256i *)(hA + 8*1), b_lo);
    _mm256_storeu_si256((__m256i *)(hA + 8*2), c_lo);
    _mm256_storeu_si256((__m256i *)(hA + 8*3), d_lo);
    _mm256_storeu_si256((__m256i *)(hA + 8*4), e_lo);
    _mm256_storeu_si256((__m256i *)(hA + 8*5), f_lo);
    _mm256_storeu_si256((__m256i *)(hA + 8*6), g_lo);
    _mm256_storeu_si256((__m256i *)(hA + 8*7), h_lo);

    _mm256_storeu_si256((__m256i *)(hB + 8*0), a_hi);
    _mm256_storeu_si256((__m256i *)(hB + 8*1), b_hi);
    _mm256_storeu_si256((__m256i *)(hB + 8*2), c_hi);
    _mm256_storeu_si256((__m256i *)(hB + 8*3), d_hi);
    _mm256_storeu_si256((__m256i *)(hB + 8*4), e_hi);
    _mm256_storeu_si256((__m256i *)(hB + 8*5), f_hi);
    _mm256_storeu_si256((__m256i *)(hB + 8*6), g_hi);
    _mm256_storeu_si256((__m256i *)(hB + 8*7), h_hi);
}

/* 16-way path (AVX-512 capable CPUs): intrinsic kernel */
static inline int scanhash_sha256d_16way(int thr_id, uint32_t *pdata,
    const uint32_t *ptarget, uint32_t max_nonce, unsigned long *hashes_done)
{
    uint32_t dataA[8 * 64] __attribute__((aligned(128)));
    uint32_t dataB[8 * 64] __attribute__((aligned(128)));
    uint32_t hashA[8 * 8] __attribute__((aligned(32)));
    uint32_t hashB[8 * 8] __attribute__((aligned(32)));
    uint32_t midA[8 * 8] __attribute__((aligned(32)));
    uint32_t preA[8 * 8] __attribute__((aligned(32)));
    uint32_t midB[8 * 8] __attribute__((aligned(32)));
    uint32_t preB[8 * 8] __attribute__((aligned(32)));
    uint32_t n = pdata[19] - 1;
    const uint32_t first_nonce = pdata[19];
    const uint32_t Htarg = ptarget[7];
    int i, j;

    uint32_t block2[16];
    /* Build big-endian view of header words for midstate and block2 */
    uint32_t pdata_be[20];
    for (i = 0; i < 20; ++i) pdata_be[i] = swab32(pdata[i]);
    cpunet_build_block2(block2, pdata_be);

    for (i = 0; i < 16; i++)
        for (j = 0; j < 8; j++)
            dataA[i * 8 + j] = block2[i];
    memcpy(dataB, dataA, sizeof(dataA));

    uint32_t midstate[8];
    sha256_init(midstate);
    /* Use big-endian word view for SHA256 midstate */
    sha256_transform(midstate, pdata_be, 0);
    memcpy(preA, midstate, 32);
    sha256d_prehash(preA, block2);
    for (i = 7; i >= 0; i--) {
        for (j = 0; j < 8; j++) {
            midA[i * 8 + j] = midstate[i];
            preA[i * 8 + j] = preA[i];
        }
    }
    memcpy(midB, midA, sizeof(midA));
    memcpy(preB, preA, sizeof(preA));

    do {
        /* normal AVX-512 path */
        for (i = 0; i < 8; i++) dataA[8 * 3 + i] = swab32(++n);
        for (i = 0; i < 8; i++) dataB[8 * 3 + i] = swab32(++n);

        sha256d_ms_16way_avx512(hashA, hashB, dataA, dataB, midA, preA, midB, preB);

        /* Report only the best lane for diagnostics to reduce overhead. */
        int best_lane = 0; uint32_t best_val = 0xffffffffU;
        for (i = 0; i < 8; i++) {
            uint32_t v = swab32(hashA[8 * 7 + i]);
            if (v < best_val) { best_val = v; best_lane = i; }
        }
        for (i = 0; i < 8; i++) {
            uint32_t v = swab32(hashB[8 * 7 + i]);
            if (v < best_val) { best_val = v; best_lane = 8 + i; }
        }
        uint32_t best_nonce = (best_lane < 8) ? swab32(dataA[8 * 3 + best_lane]) : swab32(dataB[8 * 3 + (best_lane - 8)]);
        miner_report_candidate(thr_id, pdata, best_nonce, best_val);

        for (i = 0; i < 8; i++) {
            uint32_t lane_nonce = swab32(dataA[8 * 3 + i]);
            if (lane_nonce <= max_nonce && swab32(hashA[8 * 7 + i]) <= Htarg) {
                pdata[19] = lane_nonce;
                uint32_t canon2[8];
                for (int j3 = 0; j3 < 8; j3++) canon2[j3] = swab32(hashA[8 * j3 + i]);
                if (fulltest(canon2, ptarget)) {
                    *hashes_done = n - first_nonce + 1;
                    return 1;
                }
            }
        }
        for (i = 0; i < 8; i++) {
            uint32_t lane_nonce = swab32(dataB[8 * 3 + i]);
            if (lane_nonce <= max_nonce && swab32(hashB[8 * 7 + i]) <= Htarg) {
                pdata[19] = lane_nonce;
                uint32_t canon2[8];
                for (int j3 = 0; j3 < 8; j3++) canon2[j3] = swab32(hashB[8 * j3 + i]);
                if (fulltest(canon2, ptarget)) {
                    *hashes_done = n - first_nonce + 1;
                    return 1;
                }
            }
        }
    } while (n < max_nonce && !work_restart[thr_id].restart);

    *hashes_done = n - first_nonce + 1;
    pdata[19] = n;
    return 0;
}
#endif /* __x86_64__ */

static int g_printed_sha_path = 0;
extern volatile int g_backend_force; /* defined below */

/* Feature detection helpers */
#if defined(__x86_64__)

static inline int cpu_has_avx_os(void) {
    unsigned int eax, ebx, ecx, edx;
    eax = 1; __asm__ __volatile__("cpuid":"=a"(eax),"=b"(ebx),"=c"(ecx),"=d"(edx):"a"(eax));
    if (!(ecx & (1u<<27))) return 0; /* OSXSAVE */
    unsigned int xcr0_lo=0,xcr0_hi=0; __asm__ __volatile__("xgetbv":"=a"(xcr0_lo),"=d"(xcr0_hi):"c"(0));
    return ((xcr0_lo & 0x6) == 0x6); /* XMM|YMM */
}

static inline int cpu_has_avx(void) {
    unsigned int eax, ebx, ecx, edx; eax=1; __asm__ __volatile__("cpuid":"=a"(eax),"=b"(ebx),"=c"(ecx),"=d"(edx):"a"(eax));
    return cpu_has_avx_os() && (ecx & (1u<<28));
}

static inline int cpu_has_avx2(void) {
    unsigned int eax, ebx, ecx, edx; eax=7; ecx=0; __asm__ __volatile__("cpuid":"=a"(eax),"=b"(ebx),"=c"(ecx),"=d"(edx):"a"(eax),"c"(ecx));
    return cpu_has_avx_os() && (ebx & (1u<<5));
}

static inline int cpu_has_avx512(void)
{
    unsigned int eax, ebx, ecx, edx;
    /* AVX-512F check */
    eax = 7; ecx = 0;
    __asm__ __volatile__("cpuid"
        : "=a"(eax), "=b"(ebx), "=c"(ecx), "=d"(edx)
        : "a"(eax), "c"(ecx));
    int has_avx512f = (ebx & (1u << 16)) != 0;
    if (!has_avx512f) return 0;
    /* XGETBV: require Opmask, ZMM_hi256, Hi16_ZMM plus AVX state */
    unsigned int xcr0_lo = 0, xcr0_hi = 0;
    __asm__ __volatile__("xgetbv" : "=a"(xcr0_lo), "=d"(xcr0_hi) : "c"(0));
    unsigned int need = (1u << 1) | (1u << 2) | (1u << 5) | (1u << 6);
    return ((xcr0_lo & need) == need);
}

#if defined(USE_ASM)
static inline int cpu_has_phe(void)
{
    unsigned int eax, ebx, ecx, edx;
    /* Check for extended CPUID level */
    eax = 0xC0000000u;
    __asm__ __volatile__(
        "cpuid"
        : "=a"(eax), "=b"(ebx), "=c"(ecx), "=d"(edx)
        : "a"(eax), "c"(0)
    );
    if (eax < 0xC0000001u)
        return 0;
    /* Query VIA PadLock features */
    eax = 0xC0000001u;
    __asm__ __volatile__(
        "cpuid"
        : "=a"(eax), "=b"(ebx), "=c"(ecx), "=d"(edx)
        : "a"(eax), "c"(0)
    );
    /* Bits 10 and 11 (0x00000C00) indicate SHA (PHE) availability */
    return (edx & 0x00000C00u) == 0x00000C00u;
}

static inline int cpu_has_shani(void)
{
    unsigned int eax, ebx, ecx, edx;
    /* CPUID leaf 7, subleaf 0: EBX bit 29 = SHA */
    eax = 7; ecx = 0;
    __asm__ __volatile__("cpuid"
        : "=a"(eax), "=b"(ebx), "=c"(ecx), "=d"(edx)
        : "a"(eax), "c"(ecx));
    return (ebx & (1u << 29)) != 0;
}
#endif /* USE_ASM */

#else /* !__x86_64__ */

static inline int cpu_has_avx(void) { return 0; }
static inline int cpu_has_avx2(void) { return 0; }
static inline int cpu_has_avx512(void) { return 0; }
#if defined(USE_ASM)
static inline int cpu_has_phe(void) { return 0; }
static inline int cpu_has_shani(void) { return 0; }
#endif /* USE_ASM */

#endif /* __x86_64__ */

/* Dispatcher for sha256d_ms. */
#if defined(__x86_64__) && defined(USE_ASM)
static int g_printed_sha256d_ms_path = 0;
void sha256d_ms(uint32_t *hash, uint32_t *W,
    const uint32_t *midstate, const uint32_t *prehash)
{
    if (cpu_has_phe()) {
        if (__sync_bool_compare_and_swap(&g_printed_sha256d_ms_path, 0, 1))
            applog(LOG_INFO, "sha256d_ms path: padlock-phe");
        sha256d_ms_phe(hash, W, midstate, prehash);
    } else if (cpu_has_shani()) {
        if (__sync_bool_compare_and_swap(&g_printed_sha256d_ms_path, 0, 1))
            applog(LOG_INFO, "sha256d_ms path: sha-ni");
        sha256d_ms_shani(hash, W, midstate, prehash);
    } else {
        if (__sync_bool_compare_and_swap(&g_printed_sha256d_ms_path, 0, 1))
            applog(LOG_INFO, "sha256d_ms path: scalar-c");
        sha256d_ms_c(hash, W, midstate, prehash);
    }
}
#else
/* Non-x86_64 or no ASM: always use the portable C path. */
void sha256d_ms(uint32_t *hash, uint32_t *W,
    const uint32_t *midstate, const uint32_t *prehash)
{
    sha256d_ms_c(hash, W, midstate, prehash);
}
#endif

#ifndef USE_ASM
int sha256_use_4way(void) {
#if defined(__x86_64__)
    /* SSE2 baseline on x86_64; AVX boosts throughput if available */
    (void)cpu_has_avx();
    return 1;
#else
    return 0;
#endif
}

int sha256_use_8way(void) {
    return cpu_has_avx2();
}
#endif

#ifndef USE_ASM
/* Portable 4-way/8-way init/transform used by scrypt and generic code when assembly is disabled. */
void sha256_init_4way(uint32_t *state)
{
    for (int i = 0; i < 8; i++) {
        for (int lane = 0; lane < 4; lane++)
            state[i * 4 + lane] = sha256_h[i];
    }
}

void sha256_transform_4way(uint32_t *state, const uint32_t *block, int swap)
{
    for (int lane = 0; lane < 4; lane++) {
        uint32_t st[8];
        uint32_t blk[16];
        for (int i = 0; i < 8; i++) st[i] = state[i * 4 + lane];
        for (int i = 0; i < 16; i++) blk[i] = block[i * 4 + lane];
        sha256_transform(st, blk, 0);
        for (int i = 0; i < 8; i++) state[i * 4 + lane] = st[i];
    }
}

void sha256_init_8way(uint32_t *state)
{
    for (int i = 0; i < 8; i++) {
        for (int lane = 0; lane < 8; lane++)
            state[i * 8 + lane] = sha256_h[i];
    }
}

void sha256_transform_8way(uint32_t *state, const uint32_t *block, int swap)
{
    for (int lane = 0; lane < 8; lane++) {
        uint32_t st[8];
        uint32_t blk[16];
        for (int i = 0; i < 8; i++) st[i] = state[i * 8 + lane];
        for (int i = 0; i < 16; i++) blk[i] = block[i * 8 + lane];
        sha256_transform(st, blk, 0);
        for (int i = 0; i < 8; i++) state[i * 8 + lane] = st[i];
    }
}
#endif
int scanhash_sha256d(int thr_id, uint32_t *pdata, const uint32_t *ptarget,
    uint32_t max_nonce, unsigned long *hashes_done)
{
    uint32_t data[64] __attribute__((aligned(128)));
    uint32_t hash[8] __attribute__((aligned(32)));
    uint32_t midstate[8] __attribute__((aligned(32)));
    uint32_t prehash[8] __attribute__((aligned(32)));
    uint32_t n = pdata[19] - 1;
    const uint32_t first_nonce = pdata[19];
    const uint32_t Htarg = ptarget[7];

#if defined(__x86_64__)
    /* Prefer 16-way AVX-512 when available in auto mode, or when forced */
    if (g_backend_force == 4 || (g_backend_force == 0 && cpu_has_avx512())) {
        if (__sync_bool_compare_and_swap(&g_printed_sha_path, 0, 1))
            applog(LOG_INFO, "Using 16-way AVX-512 SHA256 path");
        return scanhash_sha256d_16way(thr_id, pdata, ptarget, max_nonce, hashes_done);
    }
#endif
#ifdef HAVE_SHA256_8WAY
    if (g_backend_force == 3 || (g_backend_force == 0 && sha256_use_8way())) {
        if (__sync_bool_compare_and_swap(&g_printed_sha_path, 0, 1))
            applog(LOG_INFO, "Using 8-way AVX2 SHA256 path");
        return scanhash_sha256d_8way(thr_id, pdata, ptarget,
            max_nonce, hashes_done);
    }
#endif
#ifdef HAVE_SHA256_4WAY
    if (g_backend_force == 2 || (g_backend_force == 0 && sha256_use_4way())) {
        if (__sync_bool_compare_and_swap(&g_printed_sha_path, 0, 1))
            applog(LOG_INFO, "Using 4-way SHA256 path (AVX/XOP/SSE2)");
        return scanhash_sha256d_4way(thr_id, pdata, ptarget,
            max_nonce, hashes_done);
    }
#endif
    if (__sync_bool_compare_and_swap(&g_printed_sha_path, 0, 1))
        applog(LOG_INFO, "Using scalar SHA256 path (ASM/C/PHE auto)");

    uint32_t block2[16];
    /* Build big-endian view of header words for midstate and block2 */
    uint32_t pdata_be_all[20];
    for (int k = 0; k < 20; ++k) pdata_be_all[k] = swab32(pdata[k]);
    cpunet_build_block2(block2, pdata_be_all);

    memcpy(data, block2, 64);
    sha256d_preextend(data);

    sha256_init(midstate);
    sha256_transform(midstate, pdata_be_all, 0);
    memcpy(prehash, midstate, 32);
    sha256d_prehash(prehash, block2);

    do {
        data[3] = swab32(++n); /* big-endian W for C path */
        sha256d_ms(hash, data, midstate, prehash);

        /* Debug: bypass precheck by fulltest on this nonce when enabled */
        if (opt_debug_lax_target || opt_debug_sample_canonical) {
            uint32_t canon_dbg[8];
            for (int j = 0; j < 8; j++) canon_dbg[j] = swab32(hash[j]);
            if (fulltest(canon_dbg, ptarget)) {
                pdata[19] = n;
                *hashes_done = n - first_nonce + 1;
                return 1;
            }
        }
        miner_report_candidate(thr_id, pdata, n, swab32(hash[7]));
        if (swab32(hash[7]) <= Htarg) {
            if (opt_debug) {
                printf("\nDEBUG: Scan path found potential solution!\n");
                printf("Scan path hash[7]: %08x (swab32: %08x)\n", hash[7], swab32(hash[7]));
                printf("Target Htarg:      %08x\n", Htarg);
                // Print the full scan path result BEFORE we overwrite it
                printf("Scan path full hash: ");
                for (int j = 0; j < 8; j++) printf("%08x", swab32(hash[j]));
                printf("\n");
            }

            pdata[19] = n;

            uint32_t canon[8];
            for (int j = 0; j < 8; j++) canon[j] = swab32(hash[j]);
            if (fulltest(canon, ptarget)) {
                if (opt_debug)
                    cpunet_validate_and_print(-1, pdata, n, ptarget);
                *hashes_done = n - first_nonce + 1;
                return 1;
            }
        }
    } while (n < max_nonce && !work_restart[thr_id].restart);

    *hashes_done = n - first_nonce + 1;
    pdata[19] = n;
    return 0;
}

int cpunet_selfcheck(void)
{
    /* Build deterministic test headers and compare internal vs fast-path */
    int failures = 0;
    for (int t = 0; t < 3; ++t) {
        uint32_t hdr[20];
        for (int i = 0; i < 20; i++)
            hdr[i] = 0x12340000u * (t + 1) ^ (0x9e3779b9u * i);
        hdr[19] = 0x1000u * (t + 1) + 0xABCu; /* nonce */

        /* Canonical 87-byte preimage */
        unsigned char preimage[87];
        cpunet_serialize_preimage(preimage, hdr);

        /* Internal sha256d() over canonical 87-byte preimage */
        unsigned char internal_bytes[32];
        sha256d(internal_bytes, preimage, sizeof(preimage));

        /* Fast-path using the same midstate + prehash + sha256d_ms pipeline as scanhash */
        uint32_t pdata_equiv[20];
        for (int i = 0; i < 20; i++)
            pdata_equiv[i] = swab32(hdr[i]); /* match miner midstate representation */

        uint32_t blk2[16];
        cpunet_build_block2(blk2, pdata_equiv);

        uint32_t dataW[64];
        memcpy(dataW, blk2, 64);
        sha256d_preextend(dataW);

        uint32_t mid1[8], pre1[8];
        sha256_init(mid1);
        sha256_transform(mid1, pdata_equiv, 0);     /* midstate after first 64 bytes */
        memcpy(pre1, mid1, 32);
        sha256d_prehash(pre1, blk2);

        /* Set the target nonce in W[3] as big-endian word (C path expects BE) */
        dataW[3] = swab32(hdr[19]);

        uint32_t fp_hash[8];
        sha256d_ms(fp_hash, dataW, mid1, pre1);
        unsigned char h2_bytes[32];
        for (int i = 0; i < 8; i++)
            be32enc((uint32_t *)(h2_bytes + 4 * i), fp_hash[i]);

        /* Compare internal vs fast-path byte sequences */
        if (memcmp(internal_bytes, h2_bytes, 32) != 0) {
            char internal_hex[65], fast_hex[65];
            bin2hex(internal_hex, internal_bytes, 32);
            bin2hex(fast_hex, h2_bytes, 32);
            applog(LOG_ERR, "CPUNet self-check mismatch case %d:\n  internal=%s\n  fast    =%s", t, internal_hex, fast_hex);
            failures++;
        }

        /* Skip scanhash drive check: hashing equivalence above is sufficient. */
    }

    /* Validate CPUNet genesis block via both paths */
    {
        /* RPC fields for genesis */
        const uint32_t ver = 1u;
        const char *merk_hex = "7aa0a7ae1e223414cb807e40cd57e667b718e42aaf9306db9102fe28912b7b4e";
        const uint32_t ntime = 1723652721u;      /* 0x66C7D171 */
        const uint32_t nbits = 0x1d00ffffu;
        const uint32_t nonce = 961348305u;       /* 0x39449A71 */
        const char *expect_hex = "00000000bbffa57733938dbc05f86239f303636de4599905ab84bccfa909f49b";

        /* Construct 80-byte header as 20 LE words in miner layout */
        uint32_t header20[20] = {0};
        header20[0] = ver;
        /* header20[1..8] are zero for genesis prevhash */

        /* Decode merkle (RPC big-endian hex) -> little-endian bytes for header */
        unsigned char mr_be[32], mr_le[32];
        if (!hex2bin(mr_be, merk_hex, 32)) {
            applog(LOG_ERR, "CPUNet self-check: failed to parse genesis merkle root hex");
            return 0;
        }
        for (int i = 0; i < 32; i++) mr_le[i] = mr_be[31 - i];
        for (int i = 0; i < 8; i++)
            header20[9 + i] = le32dec(mr_le + 4 * i);

        header20[17] = ntime;
        header20[18] = nbits;
        header20[19] = nonce;

        /* Path A: canonical preimage -> sha256d() */
        unsigned char preimage[87];
        unsigned char digest_internal[32], digest_internal_rev[32];
        char digest_internal_hex[65];
        cpunet_serialize_preimage(preimage, header20);
        sha256d(digest_internal, preimage, sizeof(preimage));
        for (int i = 0; i < 32; i++) digest_internal_rev[i] = digest_internal[31 - i];
        bin2hex(digest_internal_hex, digest_internal_rev, 32);

        /* Optional debug: verify second-pass schedule preext mapping */
        debug_verify_w2_preext(header20);

        /* Path B: fast midstate pipeline */
        uint32_t pdata_equiv[20];
        for (int i = 0; i < 20; i++)
            pdata_equiv[i] = swab32(header20[i]); /* big-endian words for transform() */
        uint32_t blk2[16];
        uint32_t dataW[64];
        uint32_t mid1[8], pre1[8];
        uint32_t fp_hash[8];
        unsigned char digest_fast[32], digest_fast_rev[32];
        char digest_fast_hex[65];

        cpunet_build_block2(blk2, pdata_equiv);
        memcpy(dataW, blk2, 64);
        sha256d_preextend(dataW);
        sha256_init(mid1);
        sha256_transform(mid1, pdata_equiv, 0);
        memcpy(pre1, mid1, 32);
        sha256d_prehash(pre1, blk2);
        dataW[3] = swab32(header20[19]); /* nonce word in W (BE) */
        sha256d_ms(fp_hash, dataW, mid1, pre1);
        for (int i = 0; i < 8; i++)
            be32enc((uint32_t *)(digest_fast + 4 * i), fp_hash[i]);
        for (int i = 0; i < 32; i++) digest_fast_rev[i] = digest_fast[31 - i];
        bin2hex(digest_fast_hex, digest_fast_rev, 32);

        bool ok_internal = (strcmp(digest_internal_hex, expect_hex) == 0);
        bool ok_fast = (strcmp(digest_fast_hex, expect_hex) == 0);
        if (!ok_internal || !ok_fast) {
            applog(LOG_ERR, "CPUNet genesis mismatch:\n  internal=%s\n  fast    =%s\n  expect  =%s",
                   digest_internal_hex, digest_fast_hex, expect_hex);
            return 0;
        }
        applog(LOG_INFO, "CPUNet genesis verified: %s", expect_hex);

        /* Part 3: Re-mine genesis block with scanhash functions */
        applog(LOG_INFO, "CPUNet self-check: re-mining genesis block...");
        {
            uint32_t scan_header[20];
            uint32_t ptarget[8] = {0};
            unsigned long hashes_done = 0;
            const uint32_t start_nonce = 961340000;
            const uint32_t max_nonce = 961350000;
            int failures_remine = 0;

            // Target from nbits 0x1d00ffff
            ptarget[7] = 0x0000ffff;

            // Explicitly test scalar path by forcing backend to scalar
            {
                extern volatile int g_backend_force;
                int saved_backend = g_backend_force;
                g_backend_force = 1; /* force scalar in scanhash wrapper */
                applog(LOG_INFO, "  - Testing scalar...");
                memcpy(scan_header, header20, 80);
                scan_header[19] = start_nonce;
                if (scanhash_sha256d(0, scan_header, ptarget, max_nonce, &hashes_done)) {
                    if (scan_header[19] == nonce) {
                        applog(LOG_INFO, "    scalar OK (found nonce %u)", scan_header[19]);
                    } else {
                        applog(LOG_ERR, "    scalar FAIL: found nonce %u, expected %u", scan_header[19], nonce);
                        failures_remine++;
                    }
                } else {
                    applog(LOG_ERR, "    scalar FAIL: did not find nonce in range");
                    failures_remine++;
                }
                g_backend_force = saved_backend; /* restore */
            }

#ifdef HAVE_SHA256_4WAY
            applog(LOG_INFO, "  - Testing 4-way...");
            /* Initialize 4-way backend dispatch; skip if unsupported */
            if (!sha256_use_4way()) {
                applog(LOG_INFO, "    4-way not supported on this CPU; skipping");
            } else {
                memcpy(scan_header, header20, 80);
                scan_header[19] = start_nonce;
                if (scanhash_sha256d_4way(0, scan_header, ptarget, max_nonce, &hashes_done)) {
                if (scan_header[19] == nonce) {
                    applog(LOG_INFO, "    4-way OK (found nonce %u)", scan_header[19]);
                } else {
                    applog(LOG_ERR, "    4-way FAIL: found nonce %u, expected %u", scan_header[19], nonce);
                    failures_remine++;
                }
                } else {
                    applog(LOG_ERR, "    4-way FAIL: did not find nonce in range");
                    failures_remine++;
                }
            }
#endif
#ifdef HAVE_SHA256_8WAY
            applog(LOG_INFO, "  - Testing 8-way...");
            /* Initialize 8-way backend dispatch; skip if unsupported */
            if (!sha256_use_8way()) {
                applog(LOG_INFO, "    8-way not supported on this CPU; skipping");
            } else {
                memcpy(scan_header, header20, 80);
                scan_header[19] = start_nonce;
                if (scanhash_sha256d_8way(0, scan_header, ptarget, max_nonce, &hashes_done)) {
                if (scan_header[19] == nonce) {
                    applog(LOG_INFO, "    8-way OK (found nonce %u)", scan_header[19]);
                } else {
                    applog(LOG_ERR, "    8-way FAIL: found nonce %u, expected %u", scan_header[19], nonce);
                    failures_remine++;
                }
                } else {
                    applog(LOG_ERR, "    8-way FAIL: did not find nonce in range");
                    failures_remine++;
                }
            }
#endif
#if defined(__x86_64__)
            if (cpu_has_avx512()) {
                applog(LOG_INFO, "  - Testing 16-way...");
                memcpy(scan_header, header20, 80);
                scan_header[19] = start_nonce;
                if (scanhash_sha256d_16way(0, scan_header, ptarget, max_nonce, &hashes_done)) {
                    if (scan_header[19] == nonce) {
                        applog(LOG_INFO, "    16-way OK (found nonce %u)", scan_header[19]);
                    } else {
                        applog(LOG_ERR, "    16-way FAIL: found nonce %u, expected %u", scan_header[19], nonce);
                        failures_remine++;
                    }
                } else {
                    applog(LOG_ERR, "    16-way FAIL: did not find nonce in range");
                    failures_remine++;
                }
            }
#endif
            // Test the main wrapper
            applog(LOG_INFO, "  - Testing scanhash_sha256d wrapper...");
            memcpy(scan_header, header20, 80);
            scan_header[19] = start_nonce;
            if (scanhash_sha256d(0, scan_header, ptarget, max_nonce, &hashes_done)) {
                if (scan_header[19] == nonce) {
                    applog(LOG_INFO, "    scanhash_sha256d OK (found nonce %u)", scan_header[19]);
                } else {
                    applog(LOG_ERR, "    scanhash_sha256d FAIL: found nonce %u, expected %u", scan_header[19], nonce);
                    failures_remine++;
                }
            } else {
                applog(LOG_ERR, "    scanhash_sha256d FAIL: did not find nonce in range");
                failures_remine++;
            }

            if (failures_remine > 0) {
                failures++;
            }
        }
    }

    if (failures == 0) {
        applog(LOG_INFO, "CPUNet self-check passed (3 cases)");
        return 1;
    }
    return 0;
}

/* Report detected and selectable implementations. Called at startup. */
void sha256_print_impls(void)
{
    int avx2 = 0, avx = 0, xop = 0, sse2 = 1, phe = 0, shani = 0, avx512 = 0;
#if defined(__x86_64__) && defined(USE_ASM)
    /* Detect PHE */
    phe = cpu_has_phe();
    /* Detect AVX/AVX2/XOP approximately (match sha2-x64.S logic). */
    unsigned int eax, ebx, ecx, edx;
    eax = 1;
    __asm__ __volatile__("cpuid" : "=a"(eax), "=b"(ebx), "=c"(ecx), "=d"(edx) : "a"(eax), "c"(0));
    int osxsave = (ecx & 0x08000000u) != 0;
    int hw_avx = (ecx & 0x10000000u) != 0;
    unsigned int xcr0_lo = 0, xcr0_hi = 0;
    if (osxsave) {
        __asm__ __volatile__("xgetbv" : "=a"(xcr0_lo), "=d"(xcr0_hi) : "c"(0));
    }
    int ymm_ok = osxsave && ((xcr0_lo & 0x6u) == 0x6u);
    avx = hw_avx && ymm_ok;
#if defined(USE_AVX2)
    eax = 7; ecx = 0;
    __asm__ __volatile__("cpuid" : "=a"(eax), "=b"(ebx), "=c"(ecx), "=d"(edx) : "a"(eax), "c"(ecx));
    avx2 = ((ebx & 0x00000020u) != 0) && ymm_ok;
#endif
#if defined(USE_XOP)
    eax = 0x80000001u;
    __asm__ __volatile__("cpuid" : "=a"(eax), "=b"(ebx), "=c"(ecx), "=d"(edx) : "a"(eax), "c"(0));
    xop = ((ecx & 0x00000800u) != 0);
#endif
    shani = cpu_has_shani();
    avx512 = cpu_has_avx512();
#endif
    applog(LOG_INFO, "SHA256 backends: base-sse2=%d, avx=%d, xop=%d, avx2=%d, avx512=%d, shani=%d, phe=%d",
           sse2, avx, xop, avx2, avx512, shani, phe);
    if (avx512)
        applog(LOG_INFO, "AVX-512 detected; 16-way path planned, using best available for now");
}

/* Forward decls for scanhash variants used in micro-benchmarks */
static inline int scanhash_sha256d_scalar_c(int thr_id, uint32_t *pdata,
    const uint32_t *ptarget, uint32_t max_nonce, unsigned long *hashes_done);
#ifdef __x86_64__
static inline int scanhash_sha256d_scalar_asm(int thr_id, uint32_t *pdata,
    const uint32_t *ptarget, uint32_t max_nonce, unsigned long *hashes_done);
#if defined(USE_ASM)
static inline int scanhash_sha256d_scalar_shani(int thr_id, uint32_t *pdata,
    const uint32_t *ptarget, uint32_t max_nonce, unsigned long *hashes_done);
static inline int scanhash_sha256d_phe(int thr_id, uint32_t *pdata,
    const uint32_t *ptarget, uint32_t max_nonce, unsigned long *hashes_done);
#endif
#endif

/* Dedicated one-thread micro-benchmark for each available implementation. */
void benchmark_sha256d_all_impls(void)
{
    applog(LOG_INFO, "Running single-thread micro-benchmarks for SHA256 implementations (single core)");
    uint32_t data[64] __attribute__((aligned(128)));
    uint32_t target[8] = {0};
    target[7] = 0x0000ffff;
    memset(data, 0x55, 76);
    data[17] = swab32(time(NULL));
    memset(data + 19, 0, 52);
    data[20] = 0x80000000;
    data[31] = 0x00000280;
    unsigned long hashes_done = 0;
    struct timeval t0, t1, dt;

    /* helper macro to time a scanhash variant */
#define TIME_IT(label, CALL) \
    do { \
        data[19] = 0; hashes_done = 0; \
        gettimeofday(&t0, NULL); \
        double ms_goal = 500.0; \
        do { \
            uint32_t start = data[19]; \
            uint32_t maxn = start + 0x20000; \
            unsigned long chunk = 0; \
            CALL; \
            hashes_done += chunk; \
            data[19] = maxn; \
            gettimeofday(&t1, NULL); \
            struct timeval ts = t0; \
            timeval_subtract(&dt, &t1, &ts); \
        } while (dt.tv_sec * 1000.0 + dt.tv_usec / 1000.0 < ms_goal); \
        double hps = hashes_done / (dt.tv_sec + 1e-6 * dt.tv_usec); \
        char s[64]; \
        sprintf(s, hps >= 1e6 ? "%.0f" : "%.2f", 1e-3 * hps); \
        applog(LOG_INFO, "Benchmark %-16s: %s khash/s", label, s); \
    } while (0)

    TIME_IT("scalar-c", (chunk = 0, scanhash_sha256d_scalar_c(0, data, target, data[19] + 0x20000, &chunk)));

#ifdef __x86_64__
    TIME_IT("scalar-asm", (chunk = 0, scanhash_sha256d_scalar_asm(0, data, target, data[19] + 0x20000, &chunk)));
#endif
    /* SHA-NI scalar path only available with assembly enabled */
#if defined(__x86_64__) && defined(USE_ASM)
    if (cpu_has_shani()) {
        TIME_IT("scalar-shani", (chunk = 0, scanhash_sha256d_scalar_shani(0, data, target, data[19] + 0x20000, &chunk)));
    }
#endif
#ifdef HAVE_SHA256_4WAY
    if (sha256_use_4way()) {
        TIME_IT("4way", (chunk = 0, scanhash_sha256d_4way(0, data, target, data[19] + 0x20000, &chunk)));
    }
#endif
#ifdef HAVE_SHA256_8WAY
    if (sha256_use_8way()) {
        TIME_IT("8way", (chunk = 0, scanhash_sha256d_8way(0, data, target, data[19] + 0x20000, &chunk)));
    }
#endif
#if defined(__x86_64__)
    if (cpu_has_avx512()) {
        TIME_IT("16way", (chunk = 0, scanhash_sha256d_16way(0, data, target, data[19] + 0x20000, &chunk)));
    }
#endif
#if defined(__x86_64__) && defined(USE_ASM)
    if (cpu_has_phe()) {
        TIME_IT("padlock-phe", (chunk = 0, scanhash_sha256d_phe(0, data, target, data[19] + 0x20000, &chunk)));
    }
#endif

#undef TIME_IT
}

/* Automatic backend selection based on short micro-benchmarks. */
static double measure_backend_khs(const char *label,
    int (*fn)(int, uint32_t *, const uint32_t *, uint32_t, unsigned long *),
    uint32_t *data, uint32_t *target)
{
    unsigned long hashes_done = 0;
    struct timeval t0, t1, dt;
    gettimeofday(&t0, NULL);

    data[19] = 0;
    do {
        uint32_t start = data[19];
        uint32_t maxn = start + 0x40000;
        unsigned long chunk = 0;
        fn(0, data, target, maxn, &chunk);
        hashes_done += chunk;
        data[19] = maxn;
        gettimeofday(&t1, NULL);
        struct timeval ts = t0;
        timeval_subtract(&dt, &t1, &ts);
    } while (dt.tv_sec * 1000.0 + dt.tv_usec / 1000.0 < 250.0);

    double hps = hashes_done / (dt.tv_sec + 1e-6 * dt.tv_usec);
    char s[64];
    sprintf(s, hps >= 1e6 ? "%.0f" : "%.2f", 1e-3 * hps);
    applog(LOG_INFO, "Auto-select: %-12s -> %s khash/s", label, s);
    return hps / 1000.0; /* return KHash/s */
}

enum sha_backend { SHA_B_AUTO=0, SHA_B_SCALAR=1, SHA_B_4WAY=2, SHA_B_8WAY=3, SHA_B_16WAY=4 };
volatile int g_backend_force = SHA_B_AUTO;

void sha256_auto_select_backend(void)
{
    uint32_t data[64] __attribute__((aligned(128)));
    uint32_t target[8] = {0}; target[7] = 0x0000ffff;
    memset(data, 0x55, 76);
    data[17] = swab32(time(NULL));
    memset(data + 19, 0, 52);
    data[20] = 0x80000000; data[31] = 0x00000280;

    double best_khs = 0.0; int best = SHA_B_SCALAR;

    /* Scalar path (wrapper uses SHA-NI or C/ASM as available) */
    double s_sc = measure_backend_khs("scalar", scanhash_sha256d_scalar_c, data, target);
    if (s_sc > best_khs) { best_khs = s_sc; best = SHA_B_SCALAR; }

#ifdef __x86_64__
    /* Scalar ASM variant */
    double s_sa = measure_backend_khs("scalar-asm", scanhash_sha256d_scalar_asm, data, target);
    if (s_sa > best_khs) { best_khs = s_sa; best = SHA_B_SCALAR; }
#if defined(USE_ASM)
    if (cpu_has_shani()) {
        double s_sh = measure_backend_khs("scalar-shani", scanhash_sha256d_scalar_shani, data, target);
        if (s_sh > best_khs) { best_khs = s_sh; best = SHA_B_SCALAR; }
    }
#endif
#endif

#ifdef HAVE_SHA256_4WAY
    if (sha256_use_4way()) {
        double s4 = measure_backend_khs("4way", scanhash_sha256d_4way, data, target);
        if (s4 > best_khs) { best_khs = s4; best = SHA_B_4WAY; }
    }
#endif
// Prefer checking AVX-512 16-way first if available
#if defined(__x86_64__)
    if (cpu_has_avx512()) {
        double s16 = measure_backend_khs("16way", scanhash_sha256d_16way, data, target);
        if (s16 > best_khs) { best_khs = s16; best = SHA_B_16WAY; }
    }
#endif
#ifdef HAVE_SHA256_8WAY
    if (sha256_use_8way()) {
        double s8 = measure_backend_khs("8way", scanhash_sha256d_8way, data, target);
        if (s8 > best_khs) { best_khs = s8; best = SHA_B_8WAY; }
    }
#endif
    g_backend_force = best;
    const char *name = (best==SHA_B_16WAY?"16-way": best==SHA_B_8WAY?"8-way": best==SHA_B_4WAY?"4-way":"scalar");
    applog(LOG_INFO, "Auto-select: choosing %s backend", name);
}

/* Implement scalar C/ASM/PHE scanhash variants for micro-benchmarks. */
static inline void sha256d_ms_asm(uint32_t *hash, uint32_t *W,
    const uint32_t *midstate, const uint32_t *prehash)
{
    uint32_t st1[8];
    memcpy(st1, midstate, 32);
    sha256_transform(st1, W, 0); /* assembly back-end */
    uint32_t blk32[16];
    for (int i = 0; i < 8; i++) blk32[i] = st1[i];
    memcpy(blk32 + 8, sha256d_hash1 + 8, 32);
    sha256_init(hash);
    sha256_transform(hash, blk32, 0);
}

static inline int scanhash_sha256d_scalar_c(int thr_id, uint32_t *pdata,
    const uint32_t *ptarget, uint32_t max_nonce, unsigned long *hashes_done)
{
    uint32_t data[64] __attribute__((aligned(128)));
    uint32_t hash[8] __attribute__((aligned(32)));
    uint32_t midstate[8] __attribute__((aligned(32)));
    uint32_t prehash[8] __attribute__((aligned(32)));
    uint32_t n = pdata[19] - 1;
    const uint32_t first_nonce = pdata[19];
    const uint32_t Htarg = ptarget[7];

    uint32_t block2[16];
    uint32_t pdata_be_loc[20];
    for (int k = 0; k < 20; ++k) pdata_be_loc[k] = swab32(pdata[k]);
    cpunet_build_block2(block2, pdata_be_loc);

    memcpy(data, block2, 64);
    sha256d_preextend(data);

    sha256_init(midstate);
    /* Use C reference compressor for midstate (big-endian word view) */
    uint32_t midcpy[8]; memcpy(midcpy, midstate, 32);
    sha256_transform_ref(midcpy, pdata_be_loc, 0);
    memcpy(midstate, midcpy, 32);
    memcpy(prehash, midstate, 32);
    sha256d_prehash(prehash, block2);

    do {
        data[3] = swab32(++n);
        sha256d_ms_c(hash, data, midstate, prehash);
        if (swab32(hash[7]) <= Htarg) {
            uint32_t canon[8];
            for (int j = 0; j < 8; j++) canon[j] = swab32(hash[j]);
            if (fulltest(canon, ptarget)) {
                pdata[19] = n;
                *hashes_done = n - first_nonce + 1;
                return 1;
            }
        }
    } while (n < max_nonce && !work_restart[thr_id].restart);

    *hashes_done = n - first_nonce + 1;
    pdata[19] = n;
    return 0;
}

#ifdef __x86_64__
static inline int scanhash_sha256d_scalar_asm(int thr_id, uint32_t *pdata,
    const uint32_t *ptarget, uint32_t max_nonce, unsigned long *hashes_done)
{
    uint32_t data[64] __attribute__((aligned(128)));
    uint32_t hash[8] __attribute__((aligned(32)));
    uint32_t midstate[8] __attribute__((aligned(32)));
    uint32_t prehash[8] __attribute__((aligned(32)));
    uint32_t n = pdata[19] - 1;
    const uint32_t first_nonce = pdata[19];
    const uint32_t Htarg = ptarget[7];

    uint32_t block2[16];
    uint32_t pdata_be_loc[20];
    for (int k = 0; k < 20; ++k) pdata_be_loc[k] = swab32(pdata[k]);
    cpunet_build_block2(block2, pdata_be_loc);

    memcpy(data, block2, 64);
    sha256d_preextend(data);

    sha256_init(midstate);
    sha256_transform(midstate, pdata_be_loc, 0); /* assembly back-end */
    memcpy(prehash, midstate, 32);
    sha256d_prehash(prehash, block2);

    do {
        data[3] = swab32(++n);
        sha256d_ms_asm(hash, data, midstate, prehash);
        if (swab32(hash[7]) <= Htarg) {
            uint32_t canon[8];
            for (int j = 0; j < 8; j++) canon[j] = swab32(hash[j]);
            if (fulltest(canon, ptarget)) {
                pdata[19] = n;
                *hashes_done = n - first_nonce + 1;
                return 1;
            }
        }
    } while (n < max_nonce && !work_restart[thr_id].restart);

    *hashes_done = n - first_nonce + 1;
    pdata[19] = n;
    return 0;
}

#if defined(USE_ASM)
static inline int scanhash_sha256d_phe(int thr_id, uint32_t *pdata,
    const uint32_t *ptarget, uint32_t max_nonce, unsigned long *hashes_done)
{
    if (!cpu_has_phe()) return 0;
    uint32_t data[64] __attribute__((aligned(128)));
    uint32_t hash[8] __attribute__((aligned(32)));
    uint32_t midstate[8] __attribute__((aligned(32)));
    uint32_t prehash[8] __attribute__((aligned(32)));
    uint32_t n = pdata[19] - 1;
    const uint32_t first_nonce = pdata[19];
    const uint32_t Htarg = ptarget[7];

    uint32_t block2[16];
    uint32_t pdata_be_loc[20];
    for (int k = 0; k < 20; ++k) pdata_be_loc[k] = swab32(pdata[k]);
    cpunet_build_block2(block2, pdata_be_loc);

    memcpy(data, block2, 64);
    sha256d_preextend(data);

    sha256_init(midstate);
    sha256_transform(midstate, pdata_be_loc, 0); /* base SSE2 for midstate */
    memcpy(prehash, midstate, 32);
    sha256d_prehash(prehash, block2);

    do {
        data[3] = swab32(++n);
        sha256d_ms_phe(hash, data, midstate, prehash);
        if (swab32(hash[7]) <= Htarg) {
            uint32_t canon[8];
            for (int j = 0; j < 8; j++) canon[j] = swab32(hash[j]);
            if (fulltest(canon, ptarget)) {
                pdata[19] = n;
                *hashes_done = n - first_nonce + 1;
                return 1;
            }
        }
    } while (n < max_nonce && !work_restart[thr_id].restart);

    *hashes_done = n - first_nonce + 1;
    pdata[19] = n;
    return 0;
}
#endif /* USE_ASM */
#endif /* __x86_64__ */

#if defined(__x86_64__) && defined(USE_ASM)
/* Scalar SHA-NI variant: uses SHA-NI for midstate and double-hash per nonce */
static inline int scanhash_sha256d_scalar_shani(int thr_id, uint32_t *pdata,
    const uint32_t *ptarget, uint32_t max_nonce, unsigned long *hashes_done)
{
    if (!cpu_has_shani()) return 0;
    uint32_t data[64] __attribute__((aligned(128)));
    uint32_t hash[8] __attribute__((aligned(32)));
    uint32_t midstate[8] __attribute__((aligned(32)));
    uint32_t prehash[8] __attribute__((aligned(32)));
    uint32_t n = pdata[19] - 1;
    const uint32_t first_nonce = pdata[19];
    const uint32_t Htarg = ptarget[7];

    uint32_t block2[16];
    uint32_t pdata_be_loc[20];
    for (int k = 0; k < 20; ++k) pdata_be_loc[k] = swab32(pdata[k]);
    cpunet_build_block2(block2, pdata_be_loc);

    memcpy(data, block2, 64);
    sha256d_preextend(data);

    sha256_init(midstate);
    sha256_transform_shani(midstate, pdata_be_loc, 0);
    memcpy(prehash, midstate, 32);
    sha256d_prehash(prehash, block2);

    do {
        data[3] = swab32(++n);
        sha256d_ms_shani(hash, data, midstate, prehash);
        if (swab32(hash[7]) <= Htarg) {
            uint32_t canon[8];
            for (int j = 0; j < 8; j++) canon[j] = swab32(hash[j]);
            if (fulltest(canon, ptarget)) {
                pdata[19] = n;
                *hashes_done = n - first_nonce + 1;
                return 1;
            }
        }
    } while (n < max_nonce && !work_restart[thr_id].restart);

    *hashes_done = n - first_nonce + 1;
    /* Also compute single-lane midstate/prehash for self-check branch */
    uint32_t midstate_one[8], prehash_one[8];
    memcpy(midstate_one, (uint32_t *)midstate, 32);
    memcpy(prehash_one, (uint32_t *)prehash, 32);
    pdata[19] = n;
    return 0;
}
#endif
