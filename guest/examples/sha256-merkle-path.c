#include "../rt/om.h"
/* SHA-256 Merkle path verification: fold a leaf up to its root.
 * Input: 32-byte leaf hash, u64 LE leaf index, u64 LE depth (<= 64),
 * then depth sibling hashes of 32 bytes each, leaf level first.
 * At level i, bit i of the index decides the pair order: 0 means the
 * running hash is the left child (hash(cur || sibling)), 1 the right
 * child (hash(sibling || cur)). Output: the 32-byte root.
 * Exit 1 on short input or depth above the cap.
 * The SHA-256 block code below is duplicated from sha256.c (guests are
 * single-file; no shared library). Adds/xors/shifts only: no RV64M. */

static const uint32_t K256[64] = {
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2};

static uint32_t rotr(uint32_t x, unsigned n) { return (x >> n) | (x << (32 - n)); }

static void block(uint32_t st[8], const uint8_t *p) {
    uint32_t w[64];
    for (int i = 0; i < 16; i++)
        w[i] = ((uint32_t)p[4 * i] << 24) | ((uint32_t)p[4 * i + 1] << 16) |
               ((uint32_t)p[4 * i + 2] << 8) | (uint32_t)p[4 * i + 3];
    for (int i = 16; i < 64; i++) {
        uint32_t s0 = rotr(w[i - 15], 7) ^ rotr(w[i - 15], 18) ^ (w[i - 15] >> 3);
        uint32_t s1 = rotr(w[i - 2], 17) ^ rotr(w[i - 2], 19) ^ (w[i - 2] >> 10);
        w[i] = w[i - 16] + s0 + w[i - 7] + s1;
    }
    uint32_t a = st[0], b = st[1], c = st[2], d = st[3];
    uint32_t e = st[4], f = st[5], g = st[6], h = st[7];
    for (int i = 0; i < 64; i++) {
        uint32_t s1 = rotr(e, 6) ^ rotr(e, 11) ^ rotr(e, 25);
        uint32_t ch = (e & f) ^ (~e & g);
        uint32_t t1 = h + s1 + ch + K256[i] + w[i];
        uint32_t s0 = rotr(a, 2) ^ rotr(a, 13) ^ rotr(a, 22);
        uint32_t mj = (a & b) ^ (a & c) ^ (b & c);
        uint32_t t2 = s0 + mj;
        h = g; g = f; f = e; e = d + t1; d = c; c = b; b = a; a = t1 + t2;
    }
    st[0] += a; st[1] += b; st[2] += c; st[3] += d;
    st[4] += e; st[5] += f; st[6] += g; st[7] += h;
}

/* SHA-256 of a 64-byte message (one node pair). */
static void sha256_64(const uint8_t in[64], uint8_t out[32]) {
    uint32_t st[8] = {0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
                      0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19};
    block(st, in);
    uint8_t tail[64];
    tail[0] = 0x80;
    for (int i = 1; i < 56; i++) tail[i] = 0;
    uint64_t bits = 512;
    for (int i = 0; i < 8; i++) tail[63 - i] = (uint8_t)(bits >> (8 * i));
    block(st, tail);
    for (int i = 0; i < 8; i++)
        for (int j = 0; j < 4; j++) out[4 * i + j] = (uint8_t)(st[i] >> (24 - 8 * j));
}

int main(void) {
    const uint8_t *in = om_input();
    uint64_t len = om_input_len();
    if (len < 48) return 1;
    uint64_t index = om_read_u64(32);
    uint64_t depth = om_read_u64(40);
    if (depth > 64 || len < 48 + (depth << 5)) return 1;
    uint8_t cur[32];
    for (int i = 0; i < 32; i++) cur[i] = in[i];
    for (uint64_t level = 0; level < depth; level++) {
        const uint8_t *sib = in + 48 + (level << 5);
        uint8_t pair[64], nxt[32];
        const uint8_t *left = ((index >> level) & 1) ? sib : cur;
        const uint8_t *right = ((index >> level) & 1) ? cur : sib;
        for (int i = 0; i < 32; i++) { pair[i] = left[i]; pair[32 + i] = right[i]; }
        sha256_64(pair, nxt);
        for (int i = 0; i < 32; i++) cur[i] = nxt[i];
    }
    om_write(cur, 32);
    return 0;
}
