#include "../rt/om.h"
/* ERC-20 mixed block: a sequence of transfers applied in order.
 * Input (u64 LE): n (<= 1024), balances[n], m, then m triples
 * (from, to, amount). A transfer is a no-op if an index is out of range
 * or the sender's balance is below the amount; self-transfers with
 * sufficient balance count as successes and change nothing.
 * Output (u64 LE): number of successful transfers, then balances[n].
 * Exit 1 on short input or n above the cap. Static table: 1024 u64. */

#define MAXN 1024
static uint64_t balances[MAXN];

int main(void) {
    uint64_t len = om_input_len();
    if (len < 16) return 1;
    uint64_t n = om_read_u64(0);
    if (n > MAXN || len < 16 + (n << 3)) return 1;
    for (uint64_t i = 0; i < n; i++) balances[i] = om_read_u64(8 + (i << 3));
    uint64_t m = om_read_u64(8 + (n << 3));
    uint64_t off = 16 + (n << 3), successes = 0;
    for (uint64_t i = 0; i < m; i++) {
        if (off + 24 > len) return 1;
        uint64_t from = om_read_u64(off);
        uint64_t to = om_read_u64(off + 8);
        uint64_t amount = om_read_u64(off + 16);
        off += 24;
        if (from < n && to < n && balances[from] >= amount) {
            if (from != to) {
                balances[from] -= amount;
                balances[to] += amount;
            }
            successes++;
        }
    }
    om_write_u64(successes);
    for (uint64_t i = 0; i < n; i++) om_write_u64(balances[i]);
    return 0;
}
