#include "../rt/om.h"
/* Hot-cell increment: repeated read-modify-write of a single RAM cell.
 * Input (u64 LE): n_iter, initial cell value.
 * Output (u64 LE): final cell value (= initial + n_iter mod 2^64).
 * The cell is volatile so every iteration is a real load+store to the
 * same word. Exit 1 if input < 16 bytes. */

static volatile uint64_t hot_cell;

int main(void) {
    if (om_input_len() < 16) return 1;
    uint64_t n_iter = om_read_u64(0);
    hot_cell = om_read_u64(8);
    for (uint64_t i = 0; i < n_iter; i++) hot_cell = hot_cell + 1;
    om_write_u64(hot_cell);
    return 0;
}
