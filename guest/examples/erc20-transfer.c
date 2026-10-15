#include "../rt/om.h"
/* ERC-20-style balance transfer over an account table (token logic only,
 * as in the paper's workloads: no signatures, no Keccak paths).
 * Input (all u64 LE): n_accounts, balances[n], from_idx, to_idx, amount.
 * Output (u64 LE): success (1/0), new balance of from, new balance of to.
 * A transfer fails (success = 0, balances unchanged) if an index is out of
 * range or the sender's balance is below the amount. Exit code 0. */

int main(void) {
    if (om_input_len() < 40) return 1;
    uint64_t n = om_read_u64(0);
    if (om_input_len() < 8 + 8 * n + 24 || n > 4096) return 1;
    uint64_t from = om_read_u64(8 + 8 * n);
    uint64_t to = om_read_u64(16 + 8 * n);
    uint64_t amount = om_read_u64(24 + 8 * n);
    uint64_t ok = (from < n) & (to < n);
    uint64_t bal_from = ok ? om_read_u64(8 + 8 * from) : 0;
    uint64_t bal_to = ok ? om_read_u64(8 + 8 * to) : 0;
    ok &= (bal_from >= amount);
    if (ok && from != to) {
        bal_from -= amount;
        bal_to += amount;
    }
    om_write_u64(ok);
    om_write_u64(bal_from);
    om_write_u64(bal_to);
    return 0;
}
