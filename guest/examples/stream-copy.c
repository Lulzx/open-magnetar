#include "../rt/om.h"
/* Stream copy: output = input bytes verbatim.
 * Input: arbitrary bytes. Output: the same bytes.
 * Copies word-wise (8 bytes) then the byte tail. Assumes the output
 * region is at least as large as the input region (true for I == O).
 * Exit code 0 always. */

int main(void) {
    uint64_t len = om_input_len();
    uint64_t off = 0;
    while (off + 8 <= len) {
        om_write_u64(om_read_u64(off));
        off += 8;
    }
    if (off < len) om_write(om_input() + off, (size_t)(len - off));
    return 0;
}
