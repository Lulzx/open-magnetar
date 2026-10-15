# 07. BinaryTwist and BinaryShout

**Status:** draft · **Paper:** §4.4, ref [55] (Setty–Thaler–Zhu, ePrint 2025/105)

## Scope
Address decomposition into `d` one-hot components, the Frobenius-based one-hot
check (`Δ⋆`), address virtualization, BinaryShout for the bytecode (`Φ` with
`α_0`), BinaryTwist (`Val` reconstruction via `LT`, read/write identities, row-sum
check), the final-memory claim for the output region (C6), and the
Inc-at-random-point output used by the store router (08).

Notation: `F = |K| = 2^128`. `T = 2^n` cycles (`n ≥ 1`). A table has `K_tab = 2^a`
cells (called `NK` below, to avoid a clash with the field `K`). `d | a`, the
chunk width is `a_c = a/d ≥ 1`. Words have `L = 2^ℓ` bits (`ℓ = 6`, `L = 64`).
All points are lists of `K` with `x_1` first (C2). `r ∥ s` puts `r` in the low
variables. Labels are appended to a caller-supplied base `label` (for example
`twist/reg`, `twist/ram`, `shout/bytecode`; section 11 fixes the base labels).

## Specification

### 7.1 Address representation

An address sequence is `addr[0..T)`, each `addr[j] ∈ [0, NK)`. Split an address
into `d` chunks of `a_c` bits, **component 1 = lowest bits**:

    chunk_i(k) = (k >> (a_c·(i−1))) mod 2^{a_c},    i = 1..d,    k = Σ_i chunk_i(k)·2^{a_c(i−1)}.

The prover commits to `d` bit tables (the *components*)

    A_i : B^{a_c} × B^n → B,   A_i(u, j) = [u = chunk_i(addr[j])],

flat index `u + 2^{a_c}·j` (C2: first-listed coordinate low). The virtual full
address is `ra(k, j) = Π_i A_i(chunk_i(k), j)` with flat index `k + NK·j`. A point
`r_k ∈ K^a` splits into `r_k = r^(1) ∥ … ∥ r^(d)` with `|r^(i)| = a_c`, and the
component evaluated at the claim is `Ã_i(r^(i) ∥ s)`.
The committed bits per cycle for one address sequence are `d·2^{a_c}`.

Polynomial names in output claims: Shout `{name}/ra/{i}`; Twist
`{name}/ra{s}/{i}` (read `s ∈ [0,p)`), `{name}/wa/{i}`, `{name}/inc`; `i` is 1-based.
A claim is `(poly, point, value)` meaning `poly~(point) = value`; it is
consumed by the PCS (05, 04).

### 7.2 One-hot check (Frobenius refinement, `Δ⋆`)

Over `B` the sum of a row only gives its parity, so each component needs a
separate proof that every row `A(·, j)` has Hamming weight **at most one**.

**Collision polynomial.** For a bit row and `r, s ∈ K^{a_c}`:
`Δ(j; r, s) = Ã(r,j)·Ã(s,j) + Σ_u A(u,j)·eq(r,u)·eq(s,u)` (characteristic 2, `−=+`).
It equals `Σ_{u≠u'} A(u,j)A(u',j)·eq(r,u)·eq(s,u')`.

**Frobenius choice.** Set `s = r^(2) := (r_1², …, r_{a_c}²)`. For a bit row,
`Ã(r^(2), j) = Ã(r, j)²` (Frobenius is additive and fixes bits, and
`eq(r,u)² = eq(r^(2),u)`). Hence `Ã(r,j)·Ã(r^(2),j) = Ã(r,j)³` and the diagonal
term is `Σ_u A(u,j)·eq(r,u)³`.

**Cube identity.** Define, for each coordinate `h`,

    c_h = 1 + r_h + r_h²,    r'_h = r_h³ / c_h,    C(r) = Π_h c_h,    r' = (r'_1..r'_{a_c}).

If every `c_h ≠ 0` then for every Boolean `u`: `eq(r,u)³ = C(r)·eq(r',u)`.
Proof, per coordinate: `u_h = 1`: `r³ = c_h·r'_h` by definition. `u_h = 0`:
`(1+r)³ = 1 + r + r² + r³ = c_h + r³ = c_h·(1 + r'_h)`. (The binomial
coefficients of `(1+r)³` are `1,3,3,1 ≡ 1,1,1,1` mod 2.) The reference test
`test_onehot.py::FrobeniusIdentityTest` checks this for random `r`.

**`Δ⋆`** in this specification is

    Δ⋆(j; r) := Ã(r, j)³ + C(r)·Ã(r', j)      (= Δ(j; r, r^(2)) for bit rows).

The paper's formulas (§4.4) are correct as stated; we add what it leaves
implicit, namely a proof that `Δ⋆(j;·)` is non-zero when the row has weight ≥ 2:
the `4^{a_c}` products `eq(r,u)·eq(r^(2),u')` are linearly independent
polynomials of `r` (per coordinate the four products `(1+r)(1+r²), (1+r)r², r(1+r²), r³`
are independent in the span of `1,r,r²,r³`, and distinct coordinates use
distinct variables), so a sum of a non-empty set of them is non-zero. Its
degree in `r` is at most `3a_c`.

**Resampling rule [OM-choice].** `c_h = 0` iff `r_h ∈ {ω, ω²}`, the primitive
cube roots of unity in `GF(4) ⊂ K`. The verifier draws

    repeat: r ← challenge_ks(label ‖ b"/r", a_c)   until every c_h ≠ 0.

The whole vector is redrawn (each draw consumes fresh squeeze counters, as with
`challenge_nonzero_k`). Rationale: byte-exact, trivial to implement, and the
redraw probability is `≤ 2a_c/F`.

**Protocol** `onehot(comps, names, a_c, n)` for `m_c` components, base label `L1`
(for example `label ‖ b"/onehot"`). Components are in the order given by the
caller (Shout: `1..d`; Twist: reads `0..p−1` each with `1..d`, then the write
components `1..d`). All components share `(r, ρ)`.

1. `r, r', C` as above (label `L1 ‖ b"/r"`).
2. `ρ ← challenge_ks(L1 ‖ b"/rho", n)`; `λ ← challenge_ks(L1 ‖ b"/lambda", m_c)`.
3. Sum-check, base label `L1 ‖ b"/sc"`, `n` variables (cycle bits `j`, `x_1 = ` LSB), **degree 4**,
   claim `0`, summand

       g(j) = eq(ρ, j) · Σ_x λ_x · ( Ã_x(r, j)³ + C·Ã_x(r', j) ),

   where `Ã_x(r, j)` is the MLE over `u` only (a table of length `T`). The
   degree in each `j` variable is 4 (`eq` plus a cube).
4. The prover sends, per component `x`, `e_x = Ã_x(r ∥ s)` and `e'_x = Ã_x(r' ∥ s)`
   (`s` the sum-check point), flattened `[e_1, e'_1, e_2, e'_2, …]`, absorbed by
   `absorb_ks(L1 ‖ b"/evals", ·)`.
5. The verifier checks `eq(ρ,s)·Σ_x λ_x(e_x³ + C·e'_x) = ` the sum-check's final value.
6. Output claims, for each component in order: `(name_x, r ∥ s, e_x)`, `(name_x, r' ∥ s, e'_x)`.

An honest prover computes the claim as the actual sum of its tables (it is `0`
for valid rows); a prover with a bad row therefore fails the final check.
`Δ⋆` does not detect weight 0; the row-sum claims of 7.4/7.5 do.

**Soundness.** If some row of some component has weight ≥ 2, then
`Σ_x λ_x Σ_j eq(ρ,j)Δ⋆_x(j;r)` is a non-zero polynomial in `(λ, ρ, r)`; with
the retry slack the failure probability is `≤ (3a_c + n + 2a_c + 1)/F`, plus the
sum-check error `4n/F`: **total `≤ (5n + 5a_c + 1)/F`.**

### 7.3 Address virtualization

Input: groups `g`, each with `d` component names, an address point `r_k^g ∈ K^a`,
and terms `(c_t ∈ K^n, v_t)` meaning the already-absorbed claim
`ra~_g(r_k^g ∥ c_t) = v_t`. Output: component claims.

* `d = 1`: nothing is proven. Each term already is a component claim
  `(name_1, r_k^g ∥ c_t, v_t)`.
* `d > 1`, base label `L3`:
  1. `ν ← challenge_ks(L3 ‖ b"/nu", #terms)`, terms ordered group-major.
  2. Claim `Σ_t ν_t·v_t`. Sum-check over the `n` cycle variables (label `L3 ‖ b"/sc"`),
     **degree d+1**, summand

         Σ_g ( Σ_{t ∈ g} ν_t·eq(c_t, j) ) · Π_{i=1}^{d} Ã^g_i(r^{g,(i)}, j)

     where `Ã^g_i(r, j)` is the MLE over the chunk variables only.
  3. The prover sends, group-major then component `1..d`, `Ã^g_i(r^{g,(i)} ∥ s)`;
     absorbed with `absorb_ks(L3 ‖ b"/evals", ·)`. The verifier checks
     `Σ_g (Σ_t ν_t·eq(c_t,s))·Π_i e^g_i =` final value.
  4. Output: `(name^g_i, r^{g,(i)} ∥ s, e^g_i)`, group-major, component order.
  Soundness: `(d+1)n/F` plus `1/F` for `ν`.

Why this is correct: for Boolean `j`, `ra~(r_k, j) = Π_i Ã_i(r^(i), j)`, and
`ra~(r_k ∥ c) = Σ_j eq(c,j)·ra~(r_k, j)`.

### 7.4 BinaryShout

**Table.** `Val : B^a → K^c`, given as `c` columns, each `NK` elements of `K`
(a bit column is embedded `0↦0, 1↦1`; a small integer `z` as `t_z`; a packed group of
bits through C1's packing). The verifier evaluates `Val~_h(r_k)` itself, in
`O(c·NK)` (see Requests: this makes verification linear in the ROM size).

**Claim groups.** The caller supplies `G ≥ 1` groups. Group `g` has a cycle point
`r_g ∈ K^n`, a column subset `cols_g ⊆ [0,c)` (increasing) with claims
`rv_{g,h} = rv~_h(r_g)`, where `rv_h(j) = Σ_k ra(k,j)·Val_h(k)` is the value read in
cycle `j`, and optionally the address-bit claims `f_{g,t} = f~_t(r_g)`,
`f_t(j) = Σ_k k_t·ra(k,j)` for `t = 0..a−1` (`k_t` = bit `t`, `t = 0` the LSB).
**[OM-choice]** Multiple groups in one instance (the paper says “a constant number
of cycle points”) because the bytecode is read by claims at the Spartan point, the
register-index claims of Twist, and the router selectors. Rationale: one
virtualization and one one-hot check for all of them.

**Protocol** (base label `L`):

1. Absorb: `absorb_bytes(L‖b"/ngroups", u64le(G))`; for each group: `absorb_ks(L‖b"/point", r_g)`,
   `absorb_bytes(L‖b"/cols", Σ_h u64le(h) ‖ flag)` (`flag = 0x01` if the bit claims are present, else
   `0x00`), `absorb_ks(L‖b"/rv", rv_g)`, and if present `absorb_ks(L‖b"/bits", f_g)`.
2. For each group: `α_{g,0} ← challenge_nonzero_k(L‖b"/alpha0")`; if bit claims are present
   `α_{g,1..a} ← challenge_ks(L‖b"/alpha", a)`; `γ_g ← challenge_ks(L‖b"/gamma", |cols_g|)`.
   Then `β ← challenge_ks(L‖b"/beta", G)`.
3. `Φ_g(k) = α_{g,0} + Σ_t α_{g,t+1}·k_t + Σ_{h∈cols_g} γ_{g,h}·Val_h(k)` (the `α_{g,t}` term only
   if bits are present). Its MLE is `Φ̃_g(x) = α_{g,0} + Σ_t α_{g,t+1} x_{t+1} + Σ γ·Val~_h(x)`.
4. Sum-check (label `L‖b"/read"`, `a` variables, **degree 2**), claim

       Σ_g β_g·( α_{g,0} + Σ_t α_{g,t+1} f_{g,t} + Σ_h γ_{g,h} rv_{g,h} )  =  Σ_{k∈B^a} Σ_g β_g · ra~(k, r_g)·Φ_g(k).

   The prover sends `ε_g = ra~(r_k ∥ r_g)` for each group (`r_k` = the sum-check point),
   absorbed as `absorb_ks(L‖b"/ra_evals", ε)`. The verifier checks
   `Σ_g β_g ε_g Φ̃_g(r_k) =` final value.
5. Virtualization (7.3, label `L‖b"/virt"`): one group with `r_k` and terms `(r_g, ε_g)`, names `{name}/ra/{i}`.
6. One-hot (7.2, label `L‖b"/onehot"`), components `1..d`.
7. Output claims: virtualization claims, then one-hot claims.

**Why α_0.** The `α_{g,0}` term puts `α_{g,0}` on the left and `α_{g,0}·Σ_k ra~(k,r_g)`
on the right. As `α_{g,0} ≠ 0`, a wrong row-sum is detected deterministically
when every other claim is right; otherwise it is detected through the random linear
combination. Together with the one-hot check, every row has weight exactly one.
(Row-sum 1 for the full address implies it for each component: with weights ≤ 1
the product of component row sums is 1 only if each is 1.) No separate
non-emptiness check is needed.

**Soundness.** `≤ [2a + 1] + [(d>1) ((d+1)n + 1)] + (5n + 5a_c + 1)`, over `F`
(sum-check degree-2 rounds, coefficient batching, virtualization, one-hot). Group batching `β`
adds `1/F`.

### 7.5 BinaryTwist

**Objects.** Memory of `NK` cells of `L = 2^ℓ` bits; initial state `M_0 : B^a × B^ℓ → B`
(table index `k + NK·o`, `k` low). Cycle `j` performs `p` reads at
`ra_s(·,j)`, then one write at `wa(·,j)`, in this order. Committed: the address
components of the `p` reads and the write (7.1), and `Inc : B^ℓ × B^n → B`,
index `o + L·j`, with `Inc(·,j)` = XOR of the old and new content of the written
cell (zero if nothing changes). Virtual (never committed):

    Val(k,o,j) = M_0(k,o) + Σ_{j'<j} wa(k,j')·Inc(o,j')          (state at the START of cycle j)
    rv_s(o,j)  = Σ_k ra_s(k,j)·Val(k,o,j)                         (read value, before the write)
    wv(o,j)    = Σ_k wa(k,j)·( Val(k,o,j) + Inc(o,j) )            (written value)

Because all rows of `wa` have weight one, `wv` is the content of the written cell after the write.

**LT.** `LT(x,y) = [x < y]` for `x,y ∈ B^n` (C2, `x_1` the LSB). Its MLE:

    LT~(x, y) = Σ_{i=1}^{n} (1 + x_i)·y_i · Π_{m=i+1}^{n} (1 + x_m + y_m).

(`i` is the most significant differing bit: `x_i = 0, y_i = 1`, all higher bits equal.)
The verifier evaluates it in `n` iterations with a running suffix product
(`2n` multiplications, `n` additions). Test: `test_twist.py::LTTest`.

**Instance.** Common value point `r_o ∈ K^ℓ` and cycle point `r_c ∈ K^n`; claims
`rv_s = rv~_s(r_o ∥ r_c)` (`s ∈ [p]`) and `wv = wv~(r_o ∥ r_c)`; for each address
`x ∈ {read 0..p−1, write}` (write is `x = p`) the address-bit claims `f_{x,t} = f~_{x,t}(r_c)`,
`t = 0..a−1`, defined as in Shout. Flags: optional `final` (7.6) and `inc_extra` (7.7).
The bit claims are inputs; section 11 links them to the bytecode (register indices) or
the CPU circuit (RAM address). Twist absorbs all of these claims itself (step 1).

**Protocol** (base label `L`):

1. Absorb `L‖b"/point_o"` (`r_o`), `L‖b"/point_c"` (`r_c`), `L‖b"/rv"` (`rv`), `absorb_k(L‖b"/wv", wv)`,
   `absorb_ks(L‖b"/bits", ·)` with the `bits[x][t]` flattened `x`-major.
2. For `x = 0..p`: `α_{x,0} ← challenge_nonzero_k(L‖b"/alpha0")`, `α_{x,1..a} ← challenge_ks(L‖b"/alpha", a)`.
   Then `β ← challenge_ks(L‖b"/beta", p+1)`.
   `Φ_x(k) = α_{x,0} + Σ_t α_{x,t+1}·k_t`.
3. **Read/write sum-check** (label `L‖b"/rw"`). **[OM-choice]** One sum-check for all `p+1`
   accesses and for the address-bit and row-sum claims (the paper uses one per identity),
   binding the **cycle variables first, then the address variables** (domain index
   `j + T·k`; the committed tables keep C2 order, only the sum-check domain differs. Rationale: the
   sparse cycle-first prover algorithm, 7.9). `n + a` variables, **degree 3**, with
   `v_x = rv_x` (`x<p`), `v_p = wv`:

       claim = Σ_x β_x · ( v_x + α_{x,0} + Σ_t α_{x,t+1} f_{x,t} )
             = Σ_{j,k} eq(r_c, j) · [ Σ_x β_x · ra_x(k,j)·( V(k,j) + Φ_x(k) ) + β_p · wa(k,j)·I(j) ],

   where `ra_p := wa`, `V(k,j) = Val~(k, r_o, j)` (MLE over `o` only) and `I(j) = Inc~(r_o, j)`.
   The identity holds because `Σ_{k,j} eq(r_c,j) ra_x(k,j) V(k,j) = rv~_x(r_o ∥ r_c)`, the
   write line adds `wa·I` (`wa·(V + I)`), and the `Φ` terms contribute `Σ_k ra_x~(k,r_c)·(α_{x,0} + Σ α k_t)`.
   With `(r_j, r_k)` the challenges (first `n`, then `a`), the prover sends
   `rw_evals = [ra_0~(r_k∥r_j), …, ra_{p−1}~(…), wa~(r_k∥r_j), V~, I~]` where
   `V~ = Val~(r_k, r_o, r_j)`, `I~ = Inc~(r_o ∥ r_j)`; `p + 3` elements, absorbed
   `L‖b"/rw/evals"`. Verifier check: final value
   `= eq(r_c,r_j)·[ Σ_x β_x ε_x (V~ + Φ̃_x(r_k)) + β_p ε_p I~ ]`, with `Φ̃_x(r_k) = α_{x,0} + Σ_t α_{x,t+1}(r_k)_{t+1}`.
   **Row-sum check [OM-choice].** The `α_{x,0}` terms fold the paper's separate
   row-sum-one sum-check into this one (as in Shout, 7.4). The identities are
   homogeneous in `ra`, so without `α_{x,0}` an all-zero address would satisfy them;
   with it the equality forces `Σ_k ra_x~(k, r_c) = 1`. Combined with 7.2 this is weight exactly one.
4. **Val evaluation** (label `L‖b"/val"`, `n` variables, **degree 3**). Claim `V~ + M_0~(r_k ∥ r_o)`
   (verifier computes `M_0~`), summand
   `LT(j', r_j)·wa~(r_k, j')·Inc~(r_o, j')` over Boolean `j'`
   (with `wa~(r_k,j') = Σ_k eq(r_k,k) wa(k,j')`, a `K`-valued table). It proves
   `Val~(r_k,r_o,r_j) = M_0~(r_k,r_o) + Σ_{j'} LT~(j', r_j) wa~(r_k,j') Inc~(r_o,j')`
   (the right side is multilinear in `(k,o,j)` and agrees with `Val` on the cube).
   The prover sends `val_evals = [wa~(r_k ∥ s_v), Inc~(r_o ∥ s_v)]` (absorbed `L‖b"/val/evals"`).
   Verifier check: `LT~(s_v, r_j)·val_evals[0]·val_evals[1] =` final value.
5. **Final memory** (if requested; 7.6). 6. **Inc extra** (if requested; 7.7).
7. **Virtualization** (7.3, label `L‖b"/virt"`), groups in this order:
   read `s = 0..p−1`: `(r_k, [(r_j, ε_s)])`; write: `(r_k, [(r_j, ε_p), (s_v, val_evals[0])])`;
   if `final`: write at the final-memory point: `(r_kf, [(s_f, fin_evals[0])])`.
   For `d = 1` these terms are directly component claims.
8. **One-hot** (7.2, label `L‖b"/onehot"`) over all `(p+1)·d` components.
9. **Output claims**, in order: virtualization claims; one-hot claims; Inc claims
   `(name/inc, r_o ∥ r_j, I~)`, `(name/inc, r_o ∥ s_v, val_evals[1])`, `(name/inc, r_of ∥ s_f, fin_evals[1])` (if final),
   the extra claim (if requested). Every output is an evaluation of a committed
   polynomial, the form the PCS consumes. The paper's count `4(p+1)d + 1` etc. differs because
   we batch the one-hot check across components and count point-claims; ours are
   `(p+1)d` (+`d` if final) virtual + `2(p+1)d` one-hot + 2–4 Inc.

**Soundness** (given the input claims are for the caller's points):
`3(n+a) + 2` (rw sum-check; `2` for the degree-2 `(α,β)` batching) `+ 3n` (val)
`+ [final: 2n + m + ℓ]` `+ [d>1: (d+1)n + 1]` `+ (5n + 5a_c + 1)` (one-hot), over `F`. The
paper's `O((d·log T + (p+1)·log K + log L)/|K|)` is of the same shape.

**Verifier cost** (beyond the sum-checks, which cost `O(rounds·deg)` and `O(a)`
for `Φ̃`): `M_0~` in `O(nnz(M_0)·(a+ℓ))`, `LT~` in `O(n)`, and with `final` the
output-MLE in `O(2^m·L)`.

### 7.6 Final-memory claim (C6)

Purpose: bind the RAM contents after the last cycle in the output region to the
public output. **This protocol is ours; the paper has none.**

`final = (m, s_out, words)`: the output region is the aligned block of word indices
`[s_out·2^m, (s_out+1)·2^m)`, `s_out ∈ [0, 2^{a−m})` (so the high `a−m` bits of the word index are the
bits of `s_out`, LSB first); `words[0..2^m)` are the public 64-bit output words (from the instance; 14
fixes the layout). Define the state after the last cycle:

    Val_final(k,o) = M_0(k,o) + Σ_j wa(k,j)·Inc(o,j).

After the Val-evaluation sum-check, the verifier draws

    r_low ← challenge_ks(L‖b"/fin/r_low", m),    r_o^f ← challenge_ks(L‖b"/fin/r_o", ℓ),
    r_kf = r_low ∥ (s_out bits, LSB first)        (a coordinates).

Fixing the high coordinates to Boolean values makes `Val_final~(r_kf, r_o^f)` the MLE of the
restricted table `(k_low, o) ↦ Val_final(k_low ∥ s_out, o)` at `(r_low ∥ r_o^f)`. The verifier computes
`Out~(r_low ∥ r_o^f)` from the public words (table index `k_low + 2^m·o`, bit `o` of `words[k_low]`) and runs a
sum-check (label `L‖b"/fin"`, `n` variables, **degree 2**) with

    claim = Out~(r_low ∥ r_o^f) + M_0~(r_kf ∥ r_o^f),     summand  wa~(r_kf, j)·Inc~(r_o^f, j).

(This is `Val_final~ − M_0~` in characteristic 2.) The prover sends
`fin_evals = [wa~(r_kf ∥ s_f), Inc~(r_o^f ∥ s_f)]` (absorbed `L‖b"/fin/evals"`); the verifier
checks their product against the final value; the outputs enter as virtualization terms (7.5 step 7) and
the Inc claim. If the final memory in the region differs from `words`, the polynomial
`Val_final~(r_kf,r_o^f) − Out~` is non-zero, so the check fails except with probability `(m+ℓ)/F`
(plus `2n/F`). Both `wa` and `Inc` are bound by the rest of the Twist instance, so
this is a statement about the real final memory. `final` is used for RAM only. For the
register file there is none.

### 7.7 Inc at a random point

If `inc_extra`: after step 5, `x_o ← challenge_ks(L‖b"/incx/o", ℓ)`, `x_c ← challenge_ks(L‖b"/incx/c", n)`,
the prover sends `Inc~(x_o ∥ x_c)` (`absorb_k(L‖b"/incx/val", ·)`), and the instance emits the claim
`(name/inc, x_o ∥ x_c, value)` as an output and as the input claim of the store router (08, point `(r_o, r_j) = (x_o, x_c)`).

### 7.8 Values, width 64 and the CPU circuit

The value columns are bit vectors over `o ∈ [64]` (`ℓ = 6`, bit `o` of the word is `(w >> o) & 1`,
C5). The circuit's per-cycle read value of a register or RAM word is a 64-bit column in `W`; as a
table `rv_s(o, j)` it is flat `o + 64·j`, so Virtual Spartan's claim on that segment
at `(r_col, r_inst)` must be given to Twist as `r_o = ` the 6 column-bit coordinates and
`r_c = ` the cycle coordinates, in the variable order of `o + 64·j`. If section 10 lays cycles out as
`j = c_in + 2^c·u_inst`, then `r_c = r_{c_in} ∥ r_inst`. Section 10 must therefore store each 64-bit value
segment (`rs1`, `rs2` values, `rd` written value, RAM read value, RAM written word) with the column bit
`o` in the low 6 index bits of its column index, and `Inc` likewise as committed `o + 64·j`.

### 7.9 Parameters [OM-choice]

The vk fixes `(a, d)` per instance; `d | a`.

* **Registers:** `NK = 64` (`a = 6`, 32 architectural + 32 virtual), `p = 2`, **`d = 2`** (`a_c = 3`). Bits per cycle:
  `3·2·8 + 64 = 112` (two read addresses, one write address, `Inc`). `d = 1` is also valid
  (`3·64 + 64 = 256`, one sum-check fewer); `d = 3` gives `3·3·4 + 64 = 100`.
* **RAM:** `NK = 2^A` words, `p = 1`. **Rule: choose the smallest `d | A` with `a_c = A/d ≤ 4`**; `A` is
  a multiple of 4 by default (`A = 24`, 128 MiB: `d = 6`, `2·6·16 + 64 = 256` bits per cycle). The write
  address components are the read components (`wa_i ≡ ra_{0,i}`, committed once; RAM reads and
  writes in a cycle use the same word, which the store router needs, 08), so the
  count is `6·16 + 64 = 160`. The reference model checks this aliasing
  (`test_ram_shared_write_address`).
* **Bytecode:** `NK = ` ROM rows padded to `2^a`; `a` is padded up to a multiple of 4 if the smallest
  divisor rule would give `a_c = 1`; same rule `a_c ≤ 4`. One address sequence: `d·2^{a_c}` bits per cycle
  (for `a = 16`, `d = 4`: 64).
* Rationale: `Inc` costs 64 committed bits per cycle regardless of `d`, so components of 8–16 bits
  balance one-hot commitment against the `O(T·d)` virtualization work and `d` extra claims. Sparse one-hot
  columns are cheap to pack (§4.4).

### 7.10 Prover algorithms (informative)

None of this changes a byte of the transcript. The reference model is dense and quadratic, and uses
none of it. (The full text of [55] was not available to the author of this section; the following is
the standard structure and must be checked against it.)

* One-hot components are stored as the index `chunk_i(addr[j])` per cycle. `Ã(r,j)` is `eq_table(r)[chunk]`,
  so the one-hot check costs `O(T·d)`.
* `ra~(k, r_c)` for Shout is a histogram of addresses weighted by `eq(r_c,j)`: `O(T + NK)`.
* For the `rw` sum-check, the first `n` rounds are over cycles. `ra_x` and `wa` are sparse (one
  non-zero per cycle) and `Inc` is a single word per cycle; `Val(k,o,j)` is
  never materialized but obtained from the last write to `k` before `j` (an incremental state per
  address). After the cycle variables are bound the remaining `a` rounds work on dense tables of
  size `NK`. The expensive part is the `V` table; the target is `O(T·(p+1) + NK)` field operations
  plus `O(T·L)` bit operations.
* The `LT` table needed for the `val` sum-check is built in `O(T)` by the recurrence on the
  most-significant differing bit.

### 7.11 Resolved questions

1. **d.** Registers `d = 2` (`d = 1` allowed); RAM and bytecode `a_c ≤ 4`, 7.9. **[OM-choice]**
2. **RAM address space.** Bounded, word-addressed, `2^A` words in the vk; out-of-range is unprovable (C5).
3. **`M_0`.** The verifier evaluates `M_0~` itself; `m0_eval` is a callable. It is sparse (data segments and inputs, C6), so `O(nnz)`.
4. **Outputs.** The final-memory claim of 7.6 on the output region, not explicit output cycles. **[OM-choice]** Rationale: no extra cycles, one sum-check of `n` rounds, and the output region is an aligned
   subcube.
5. **Prover algorithm.** Informative only, 7.10.
6. Also **[OM-choice]**: one `rw` sum-check for all accesses with the row-sum folded in via `α_{x,0}`;
   cycle-first variable order; multi-group Shout claims; shared `(r, ρ)` across components.

### 7.12 Reference model

Modules: `reference/openmagnetar/onehot.py` (`EvalClaim`, address decomposition, `onehot_*`, `virt_*`),
`shout.py` (`shout_prove/verify`, `shout_honest_claims`), `twist.py` (`twist_prove/verify`, `build_witness`,
`honest_claims`, `lt_eval`). Tests: `test_onehot.py` (cube identity, Δ⋆ equals the collision polynomial,
weight-2 rejected, `c_h = 0` detection, virtualization), `test_shout.py` (`d = 1,2,3`, multi-group, wrong
value, wrong bit, weight 2, weight 0), `test_twist.py` (`p = 1,2`, `d = 1,2,3`, final memory, `inc_extra`,
inconsistent read, wrong write value, weight 2/0, wrong increment, wrong final memory, wrong region, shared
write address), `test_vectors_07_08.py`. Vectors: `reference/vectors/07-twist-shout/` via
`reference/gen_vectors_07_08.py`.

## Requests to other sections

* **02/11:** base labels `shout/bytecode`, `twist/reg`, `twist/ram`; labels used here are listed in 7.2–7.7.
* **06/10:** value segments laid out as in 7.8 (`o` in the low 6 bits); Twist gets `r_c`, `r_o` in that order.
* **10:** (i) RAM: `wa ≡ ra`; non-RAM cycles access word 0 with `wv = rv` (zero `Inc`); register `x0`: writes
  have zero `Inc` (C5). (ii) The `Inc`-on-non-store-cycle zero check is enforced by the store router (08),
  not by Twist.
* **11:** the register-index bit claims and RAM address-bit claims are inputs to Twist; list how they are
  discharged. The bytecode Shout takes several claim groups (7.4). The verifier computes `Val~` of the ROM in
  `O(c·NK)`, linear in program size; a committed-ROM variant would need 04/05 and is out of scope for v1.
* **13:** soundness formulas of 7.2–7.5.
* **14:** output region `(m, s_out)` and the words `words` come from the instance.
