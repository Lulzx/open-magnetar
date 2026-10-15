#include "../rt/om.h"
/* Input: 8 bytes LE n. Output: 8 bytes LE fib(n) mod 2^64. Exit code 0. */
int main(void) {
    if (om_input_len() < 8) return 1;
    uint64_t n = om_read_u64(0), a = 0, b = 1;
    for (uint64_t i = 0; i < n; i++) { uint64_t t = a + b; a = b; b = t; }
    om_write_u64(a);
    return 0;
}
