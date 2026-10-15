#include "../rt/om.h"
/* Binary search over sorted keys held in the input region.
 * Input (u64 LE): n, keys[n] (sorted ascending), q, queries[q].
 * Output (u64 LE per query): index of the key, or 2^64-1 if absent.
 * With duplicate keys, some matching index (not necessarily first).
 * Exit 1 on short input. */

int main(void) {
    uint64_t len = om_input_len();
    if (len < 16) return 1;
    uint64_t n = om_read_u64(0);
    if (n > (len >> 3) || len < 16 + (n << 3)) return 1;
    uint64_t q = om_read_u64(8 + (n << 3));
    if (q > (len >> 3) || len < 16 + (n << 3) + (q << 3)) return 1;
    for (uint64_t i = 0; i < q; i++) {
        uint64_t want = om_read_u64(16 + (n << 3) + (i << 3));
        uint64_t lo = 0, hi = n, ans = ~(uint64_t)0; /* search in [lo, hi) */
        while (lo < hi) {
            uint64_t mid = (lo + hi) >> 1;
            uint64_t v = om_read_u64(8 + (mid << 3));
            if (v == want) { ans = mid; break; }
            if (v < want) lo = mid + 1; else hi = mid;
        }
        om_write_u64(ans);
    }
    return 0;
}
