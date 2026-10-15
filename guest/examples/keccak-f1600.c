#include "../rt/om.h"
/* Keccak-f[1600] permutation, applied once (24 rounds).
 * Input: 200 bytes = 25 u64 lanes, little-endian, lane index x + 5*y.
 * Output: the permuted state, same encoding. Exit 1 if input < 200 bytes.
 * Rotations via shifts only. Uses the compact rho/pi walk (rotc/piln
 * tables) from the Keccak reference; round constants per FIPS 202. */

static const uint64_t RC[24] = {
    0x0000000000000001ULL, 0x0000000000008082ULL, 0x800000000000808AULL, 0x8000000080008000ULL,
    0x000000000000808BULL, 0x0000000080000001ULL, 0x8000000080008081ULL, 0x8000000000008009ULL,
    0x000000000000008AULL, 0x0000000000000088ULL, 0x0000000080008009ULL, 0x000000008000000AULL,
    0x000000008000808BULL, 0x800000000000008BULL, 0x8000000000008089ULL, 0x8000000000008003ULL,
    0x8000000000008002ULL, 0x8000000000000080ULL, 0x000000000000800AULL, 0x800000008000000AULL,
    0x8000000080008081ULL, 0x8000000000008080ULL, 0x0000000080000001ULL, 0x8000000080008008ULL};
static const uint8_t ROTC[24] = {1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14,
                                 27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44};
static const uint8_t PILN[24] = {10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4,
                                 15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1};

static uint64_t rotl(uint64_t x, unsigned n) {
    n &= 63;
    return n ? ((x << n) | (x >> (64 - n))) : x;
}

static void keccak_f1600(uint64_t st[25]) {
    for (int round = 0; round < 24; round++) {
        uint64_t bc[5], t;
        /* theta */
        for (int i = 0; i < 5; i++)
            bc[i] = st[i] ^ st[i + 5] ^ st[i + 10] ^ st[i + 15] ^ st[i + 20];
        for (int i = 0; i < 5; i++) {
            int prev = (i == 0) ? 4 : i - 1;
            int nxt = (i == 4) ? 0 : i + 1;
            t = bc[prev] ^ rotl(bc[nxt], 1);
            for (int j = 0; j < 25; j += 5) st[j + i] ^= t;
        }
        /* rho + pi */
        t = st[1];
        for (int i = 0; i < 24; i++) {
            int j = PILN[i];
            uint64_t tmp = st[j];
            st[j] = rotl(t, ROTC[i]);
            t = tmp;
        }
        /* chi */
        for (int j = 0; j < 25; j += 5) {
            for (int i = 0; i < 5; i++) bc[i] = st[j + i];
            for (int i = 0; i < 5; i++) {
                int n1 = (i == 4) ? 0 : i + 1;
                int n2 = (i >= 3) ? i - 3 : i + 2;
                st[j + i] ^= (~bc[n1]) & bc[n2];
            }
        }
        /* iota */
        st[0] ^= RC[round];
    }
}

int main(void) {
    if (om_input_len() < 200) return 1;
    uint64_t st[25];
    for (int i = 0; i < 25; i++) st[i] = om_read_u64((uint64_t)i << 3);
    keccak_f1600(st);
    for (int i = 0; i < 25; i++) om_write_u64(st[i]);
    return 0;
}
