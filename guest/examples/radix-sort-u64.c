#include "../rt/om.h"
/* LSD radix sort of u64 keys, base 2^16 (4 passes, masks/shifts only).
 * Input (u64 LE): n (<= 8192), keys[n]. Output (u64 LE): keys sorted
 * ascending, n entries. Exit 1 on short input or n above the cap.
 * Static RAM: two 8192-entry u64 buffers (128 KiB) and one 65536-entry
 * u32 counting array (256 KiB). Stable. */

#define MAXN 8192
#define RADIX 65536

static uint64_t buf_a[MAXN], buf_b[MAXN];
static uint32_t cnt[RADIX];

int main(void) {
    uint64_t len = om_input_len();
    if (len < 8) return 1;
    uint64_t n = om_read_u64(0);
    if (n > MAXN || len < 8 + (n << 3)) return 1;
    for (uint64_t i = 0; i < n; i++) buf_a[i] = om_read_u64(8 + (i << 3));

    uint64_t *src = buf_a, *dst = buf_b;
    for (uint64_t pass = 0; pass < 4; pass++) {
        uint64_t shift = pass << 4; /* 0, 16, 32, 48 */
        for (uint64_t i = 0; i < RADIX; i++) cnt[i] = 0;
        for (uint64_t i = 0; i < n; i++) cnt[(src[i] >> shift) & 0xFFFF]++;
        uint32_t run = 0;
        for (uint64_t i = 0; i < RADIX; i++) {
            uint32_t c = cnt[i];
            cnt[i] = run;
            run += c;
        }
        for (uint64_t i = 0; i < n; i++) {
            uint64_t k = src[i];
            dst[cnt[(k >> shift) & 0xFFFF]++] = k;
        }
        uint64_t *tmp = src; src = dst; dst = tmp;
    }
    /* 4 (even) passes: result is back in buf_a == src. */
    for (uint64_t i = 0; i < n; i++) om_write_u64(src[i]);
    return 0;
}
