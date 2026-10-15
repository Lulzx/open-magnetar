#include "../rt/om.h"
/* Pointer chase over an index chain held in the input region.
 * Input (u64 LE): n, next[n] (each < n for a well-formed chain), steps.
 * Start at index 0, follow `steps` links: cur = next[cur].
 * Output (u64 LE): final index, XOR of every visited index (the start
 * index 0 and the index after each step; 0 contributes nothing).
 * Exit 1 on short input, n == 0, or a next[] entry >= n. */

int main(void) {
    uint64_t len = om_input_len();
    if (len < 24) return 1;
    uint64_t n = om_read_u64(0);
    if (n == 0 || n > (len >> 3)) return 1;
    if (len < 16 + (n << 3)) return 1;
    uint64_t steps = om_read_u64(8 + (n << 3));
    uint64_t cur = 0, acc = 0;
    for (uint64_t i = 0; i < steps; i++) {
        cur = om_read_u64(8 + (cur << 3));
        if (cur >= n) return 1;
        acc ^= cur;
    }
    om_write_u64(cur);
    om_write_u64(acc);
    return 0;
}
