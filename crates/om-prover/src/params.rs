//! Soundness calculator: the ledger of spec §13. Mirrors
//! `reference/openmagnetar/params.py`.
//!
//! Every row is a reduction of the protocol. Errors of field-sized
//! steps are kept as numerators over `|K| = 2^128` (`rbr_num` = worst
//! single round, `tot_num` = whole reduction). PCS rows whose error is
//! not of the form `c/|K|` carry `bits_direct` directly.

use om_pcs::ligerito::{LigeritoParams, make_params};

/// `log2 |K|`.
pub const FIELD_BITS: f64 = 128.0;
/// Target per-round soundness in bits.
pub const TARGET: u32 = 120;
/// Random-oracle queries assumed for the hash row (§13.7), as `log2`.
pub const QUERY_BUDGET_LOG2: u32 = 64;
/// `log2(committed bits per cycle ~ 1572)` rounded up (§13.3).
pub const ELL_OFFSET: usize = 11;

/// Machine shape the ledger is computed for (Python `Machine`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Machine {
    /// `T = 2^log_t` cycles.
    pub log_t: usize,
    /// `log2` cycles per instance (§10.2).
    pub c: usize,
    /// Row variables (§10.2).
    pub rho: usize,
    /// Column variables (§10.2).
    pub nu: usize,
    /// State segment log size (§10.9).
    pub lam: usize,
    /// Register file `2^6`, `d = 2`.
    pub reg_a: usize,
    /// Register Twist components.
    pub reg_d: usize,
    /// Register Twist reads.
    pub reg_p: usize,
    /// RAM words `2^A`, `d = 6`.
    pub ram_a: usize,
    /// RAM Twist components.
    pub ram_d: usize,
    /// Output region log size (§7.6).
    pub out_m: usize,
    /// Bytecode rows `2^16`, `d = 4`.
    pub rom_a: usize,
    /// Bytecode Shout components.
    pub rom_d: usize,
    /// Shout claim groups (unused by the formulas, kept for parity).
    pub rom_groups: usize,
    /// Upper bound on the number of Mosaic claims (§5.7); `<= 256`.
    pub mosaic_claims: usize,
    /// `ell - log_t` estimate.
    pub ell_offset: usize,
}

impl Machine {
    /// A machine for `T = 2^log_t` with Python's default shape.
    pub fn new(log_t: usize) -> Machine {
        Machine {
            log_t,
            c: 2,
            rho: 10,
            nu: 14,
            lam: 8,
            reg_a: 6,
            reg_d: 2,
            reg_p: 2,
            ram_a: 24,
            ram_d: 6,
            out_m: 10,
            rom_a: 16,
            rom_d: 4,
            rom_groups: 3,
            mosaic_claims: 128,
            ell_offset: ELL_OFFSET,
        }
    }

    /// `s = log_t - c`.
    pub fn s(&self) -> usize {
        self.log_t - self.c
    }

    /// `log2` size of the Mosaic polynomial `G` (estimate).
    pub fn ell(&self) -> usize {
        self.log_t + self.ell_offset
    }

    /// Variables of the packed polynomial.
    pub fn n_pack(&self) -> usize {
        self.ell() - 7
    }
}

/// One ledger row (Python `Row`).
#[derive(Clone, Debug, PartialEq)]
pub struct Row {
    /// Step name.
    pub step: String,
    /// Spec section.
    pub section: String,
    /// Error formula (display).
    pub formula: String,
    /// Worst round, numerator over `|K|`.
    pub rbr_num: Option<f64>,
    /// Whole reduction, numerator over `|K|`.
    pub tot_num: Option<f64>,
    /// Bits directly, for non-field rows (queries, gap, hash).
    pub bits_direct: Option<f64>,
    /// Whether the bound is provable (not conjectured).
    pub provable: bool,
}

impl Row {
    fn field(step: &str, section: &str, formula: &str, rbr_num: f64, tot_num: f64) -> Row {
        Row {
            step: step.to_string(),
            section: section.to_string(),
            formula: formula.to_string(),
            rbr_num: Some(rbr_num),
            tot_num: Some(tot_num),
            bits_direct: None,
            provable: true,
        }
    }

    fn direct(step: &str, section: &str, formula: &str, bits: f64, provable: bool) -> Row {
        Row {
            step: step.to_string(),
            section: section.to_string(),
            formula: formula.to_string(),
            rbr_num: None,
            tot_num: None,
            bits_direct: Some(bits),
            provable,
        }
    }

    /// Per-round soundness in bits (the paper's quantity, §13.2).
    pub fn rbr_bits(&self) -> f64 {
        if let Some(b) = self.bits_direct {
            return b;
        }
        match self.rbr_num {
            Some(v) if v != 0.0 => FIELD_BITS - v.log2(),
            _ => f64::INFINITY,
        }
    }

    /// Whole-reduction soundness in bits.
    pub fn tot_bits(&self) -> f64 {
        if let Some(b) = self.bits_direct {
            return b;
        }
        match self.tot_num {
            Some(v) if v != 0.0 => FIELD_BITS - v.log2(),
            _ => f64::INFINITY,
        }
    }
}

fn onehot(tag: &str, sec: &str, n: usize, a_c: usize) -> Row {
    Row::field(
        &format!("{tag}: one-hot (Delta*)"),
        sec,
        "4n sum-check + (n + 5a_c + 1) polynomial",
        (4usize.max(n + 5 * a_c + 1)) as f64,
        (5 * n + 5 * a_c + 1) as f64,
    )
}

fn virt(tag: &str, d: usize, n: usize) -> Vec<Row> {
    if d == 1 {
        return Vec::new();
    }
    vec![Row::field(
        &format!("{tag}: address virtualization"),
        "07 7.3",
        "(d+1)n + 1",
        ((d + 1).max(1)) as f64,
        ((d + 1) * n + 1) as f64,
    )]
}

/// The field-sized rows (Spartan, Shout, Twists, routers, Mosaic, ring
/// switching).
pub fn field_rows(m: &Machine) -> Vec<Row> {
    let (n, s, rho, nu, lam) = (m.log_t, m.s(), m.rho, m.nu, m.lam);
    // Virtual Spartan (§6.3, §6.5), 2 relations in lockstep.
    let mut r: Vec<Row> = vec![
        Row::field(
            "Spartan outer: tau (both relations)",
            "06 6.3",
            "2(rho+s)",
            (rho + s) as f64,
            (2 * (rho + s)) as f64,
        ),
        Row::field(
            "Spartan outer: sum-check, lockstep bin+fld",
            "06 6.3",
            "2*3*(rho+s); shared instance rounds 6 per round",
            6.0,
            (6 * (rho + s)) as f64,
        ),
        Row::field(
            "Spartan: alpha batching of 6 terminal values",
            "06 6.3",
            "1",
            1.0,
            1.0,
        ),
        Row::field(
            "Spartan inner sum-check (single, both relations)",
            "06 6.3",
            "2 nu",
            2.0,
            (2 * nu) as f64,
        ),
        Row::field(
            "Segment split (identity 6.2)",
            "06 6.5",
            "0 (exact)",
            0.0,
            0.0,
        ),
        Row::field(
            "Cross-step (X1)-(X3)",
            "06 6.6",
            "3(lam+s)+2",
            (lam + s + 2) as f64,
            (3 * (lam + s) + 2) as f64,
        ),
    ];
    // Shout bytecode (§7.4).
    let ca = m.rom_a / m.rom_d;
    r.push(Row::field(
        "Shout bytecode: read sum-check + alpha/gamma/beta batching",
        "07 7.4",
        "2a + 2",
        2.0,
        (2 * m.rom_a + 2) as f64,
    ));
    r.extend(virt("Shout bytecode", m.rom_d, n));
    r.push(onehot("Shout bytecode", "07 7.2", n, ca));
    // Twist registers and RAM (§7.5, §7.6, §7.7).
    for (tag, a, d, fin) in [
        ("Twist reg", m.reg_a, m.reg_d, false),
        ("Twist RAM", m.ram_a, m.ram_d, true),
    ] {
        r.push(Row::field(
            &format!("{tag}: read/write sum-check + (alpha,beta) batching"),
            "07 7.5",
            "3(n+a) + 2",
            3.0,
            (3 * (n + a) + 2) as f64,
        ));
        r.push(Row::field(
            &format!("{tag}: Val evaluation (LT)"),
            "07 7.5",
            "3n",
            3.0,
            (3 * n) as f64,
        ));
        if fin {
            r.push(Row::field(
                &format!("{tag}: final-memory sum-check"),
                "07 7.6",
                "2n + m + ell_word",
                (2usize.max(m.out_m + 6)) as f64,
                (2 * n + m.out_m + 6) as f64,
            ));
        }
        r.extend(virt(tag, d, n));
        r.push(onehot(tag, "07 7.2", n, a / d));
    }
    r.push(Row::field(
        "Twist RAM: Inc at random point (inc_extra)",
        "07 7.7",
        "0 (exact)",
        0.0,
        0.0,
    ));
    // Router (§08).
    r.push(Row::field(
        "Router shift",
        "08 8.2",
        "4(n+15)",
        4.0,
        (4 * (n + 15)) as f64,
    ));
    r.push(Row::field(
        "Router store",
        "08 8.3",
        "6(n+9)",
        6.0,
        (6 * (n + 9)) as f64,
    ));
    // Mosaic batching (§5.7) and ring switching (§4.5).
    r.push(Row::field(
        "Mosaic batching + lifting sum-check",
        "05 5.7",
        "2 ell + (#claims - 1)",
        (2usize.max(m.mosaic_claims - 1)) as f64,
        (2 * m.ell() + m.mosaic_claims - 1) as f64,
    ));
    r.push(Row::field(
        "Ring switching",
        "04 4.5",
        "7 + 2 n_pack",
        7.0,
        (7 + 2 * m.n_pack()) as f64,
    ));
    r
}

/// The per-level Ligerito rows.
pub fn pcs_rows(m: &Machine, p: &LigeritoParams, profile: &str) -> Vec<Row> {
    let _ = m;
    let prov = profile == "provable-120";
    let mut r: Vec<Row> = Vec::new();
    for i in 0..p.levels() {
        let (k, t, rate) = (p.ks[i], p.ts[i], p.rs[i]);
        let rho = 2f64.powi(-(rate as i32));
        let n_cw = (1usize << p.log_codeword(i)) as f64;
        r.push(Row::field(
            &format!("Ligerito L{i}: sum-check ({k} rounds)"),
            "04 4.4",
            "2k",
            2.0,
            (2 * k) as f64,
        ));
        r.push(Row::field(
            &format!("Ligerito L{i}: beta batching of queries"),
            "04 4.4",
            "t",
            t as f64,
            t as f64,
        ));
        let gb = p.reps(i) as f64 * (FIELD_BITS - (k as f64 * n_cw).log2());
        r.push(Row::direct(
            &format!("Ligerito L{i}: proximity gap (reps={})", p.reps(i)),
            "04 4.7",
            "(k N / |K|)^reps",
            gb,
            prov,
        ));
        let qb = if prov {
            t as f64 * -((1.0 + rho) / 2.0).log2()
        } else {
            (t * rate) as f64
        };
        r.push(Row::direct(
            &format!("Ligerito L{i}: queries (t={t})"),
            "04 4.7",
            if prov {
                "((1+rho)/2)^t"
            } else {
                "rho^t (conjectured)"
            },
            qb,
            prov,
        ));
    }
    r
}

/// The hash-binding row (§13.7).
pub fn hash_row(q_log2: u32, digest_bits: u32) -> Row {
    Row::direct(
        &format!("Hash: Merkle/commitment binding, Q=2^{q_log2} oracle queries"),
        "13 13.7",
        "Q^2 / 2^(digest_bits)",
        f64::from(digest_bits) - 2.0 * f64::from(q_log2),
        true,
    )
}

/// A full ledger (Python `Ledger`).
#[derive(Clone, Debug)]
pub struct Ledger {
    /// Machine shape.
    pub machine: Machine,
    /// PCS profile name.
    pub profile: String,
    /// Ligerito parameters.
    pub params: LigeritoParams,
    /// All rows: field, then PCS, then hash.
    pub rows: Vec<Row>,
}

impl Ledger {
    /// Whether every row is provable under `provable-120`.
    pub fn provable(&self) -> bool {
        self.profile == "provable-120" && self.rows.iter().all(|r| r.provable)
    }

    /// The `k` weakest rows (by per-round bits, or by total bits if
    /// `by_total`).
    pub fn weakest(&self, k: usize, by_total: bool) -> Vec<Row> {
        let mut rows = self.rows.clone();
        rows.sort_by(|a, b| {
            let (x, y) = if by_total {
                (a.tot_bits(), b.tot_bits())
            } else {
                (a.rbr_bits(), b.rbr_bits())
            };
            x.partial_cmp(&y).expect("bits are not NaN")
        });
        rows.truncate(k);
        rows
    }

    /// Minimum per-round bits over all rows.
    pub fn min_rbr_bits(&self) -> f64 {
        self.rows
            .iter()
            .map(Row::rbr_bits)
            .fold(f64::INFINITY, f64::min)
    }

    /// `-log2` of the sum of every reduction's total error (union bound).
    pub fn total_error_bits(&self) -> f64 {
        let s: f64 = self.rows.iter().map(|r| 2f64.powf(-r.tot_bits())).sum();
        -s.log2()
    }
}

/// Build a ledger (Python `ledger`): default machine from `log_t` and
/// default parameters `make_params(n_pack, profile, r = 2)`, unless
/// overridden.
pub fn ledger(
    log_t: usize,
    profile: &str,
    machine: Option<Machine>,
    params: Option<LigeritoParams>,
) -> Ledger {
    let m = machine.unwrap_or_else(|| Machine::new(log_t));
    let p = params.unwrap_or_else(|| make_params(m.n_pack(), profile, 2));
    let mut rows = field_rows(&m);
    rows.extend(pcs_rows(&m, &p, profile));
    rows.push(hash_row(QUERY_BUDGET_LOG2, 256));
    Ledger {
        machine: m,
        profile: profile.to_string(),
        params: p,
        rows,
    }
}

/// Expected proof size of one opening, in bytes (§13.5). Repetition
/// (`gs > 1`) costs only the larger next-level polynomial.
pub fn proof_size_bytes(p: &LigeritoParams, n_ring: bool) -> f64 {
    let mut total = 0.0f64;
    for i in 0..p.levels() {
        let (k, t) = (p.ks[i], p.ts[i]);
        let lb = p.log_codeword(i);
        let n_cw = (1usize << lb) as f64;
        let q = n_cw * (1.0 - (1.0 - 1.0 / n_cw).powf(t as f64));
        let cols = q * 16.0 * (1usize << k) as f64;
        let auth = q * (lb as f64 - q.log2() + 2.0).max(0.0) * 32.0;
        total += cols + auth + 32.0 + 32.0 * k as f64;
    }
    total += 16.0 * (1usize << p.n_final()) as f64;
    if n_ring {
        total += 2048.0 + 32.0 * p.n as f64;
    }
    total
}

/// The text report (Python `report`).
pub fn report(log_t: usize, profile: &str) -> String {
    let l = ledger(log_t, profile, None, None);
    let gs = if l.params.gs.is_empty() {
        "1".to_string()
    } else {
        format!("{:?}", l.params.gs)
    };
    let mut out = vec![
        format!(
            "T=2^{log_t} profile={profile} provable={} n_pack={} ks={:?} gs={gs} ts={:?}",
            l.provable(),
            l.machine.n_pack(),
            l.params.ks,
            l.params.ts
        ),
        format!("{:62} {:>9} {:>10}", "step", "rbr bits", "total bits"),
    ];
    for r in &l.rows {
        out.push(format!(
            "{:62} {:9.1} {:10.1}",
            r.step,
            r.rbr_bits(),
            r.tot_bits()
        ));
    }
    out.push(format!(
        "min per-round bits {:.1}; union of all totals: {:.1} bits; proof ~{:.0} KiB",
        l.min_rbr_bits(),
        l.total_error_bits(),
        proof_size_bytes(&l.params, true) / 1024.0
    ));
    out.join("\n")
}
