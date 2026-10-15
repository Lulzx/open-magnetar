#include "../rt/om.h"
/* ERC-20 transferFrom over account/allowance tables (u64 model).
 * Input (u64 LE): n (<= 64), balances[n], allowances[n*n] row-major
 * (allowance[owner][spender]), spender, from, to, amount.
 * Output (u64 LE): success (1/0), balance of from, balance of to,
 * allowance[from][spender] after the call. The transfer succeeds iff all
 * indices are in range, allowance >= amount and balance[from] >= amount;
 * on success the allowance is decremented by amount (no 2^256-1 infinite
 * allowance special case in this u64 model) and the balance moves (a
 * self-transfer leaves the balance unchanged but still spends allowance).
 * If any index is out of range, output is 0,0,0,0. Exit 1 on short
 * input or n above the cap; tables are static 64 and 64x64 u64. */

#define MAXN 64
static uint64_t balances[MAXN];
static uint64_t allowances[MAXN][MAXN];

int main(void) {
    uint64_t len = om_input_len();
    if (len < 8) return 1;
    uint64_t n = om_read_u64(0);
    if (n > MAXN) return 1;
    uint64_t off = 8;
    for (uint64_t i = 0; i < n; i++) {
        if (off + 8 > len) return 1;
        balances[i] = om_read_u64(off);
        off += 8;
    }
    for (uint64_t i = 0; i < n; i++)
        for (uint64_t j = 0; j < n; j++) {
            if (off + 8 > len) return 1;
            allowances[i][j] = om_read_u64(off);
            off += 8;
        }
    if (off + 32 > len) return 1;
    uint64_t spender = om_read_u64(off);
    uint64_t from = om_read_u64(off + 8);
    uint64_t to = om_read_u64(off + 16);
    uint64_t amount = om_read_u64(off + 24);

    uint64_t ok = (spender < n) & (from < n) & (to < n);
    if (!ok) {
        om_write_u64(0); om_write_u64(0); om_write_u64(0); om_write_u64(0);
        return 0;
    }
    ok = (allowances[from][spender] >= amount) & (balances[from] >= amount);
    if (ok) {
        allowances[from][spender] -= amount;
        if (from != to) {
            balances[from] -= amount;
            balances[to] += amount;
        }
    }
    om_write_u64(ok);
    om_write_u64(balances[from]);
    om_write_u64(balances[to]);
    om_write_u64(allowances[from][spender]);
    return 0;
}
