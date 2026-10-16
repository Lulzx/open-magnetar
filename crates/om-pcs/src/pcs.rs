//! The PCS trait and its Ligerito / bit-vector instantiations (spec 04 §4.1).
//! Mirrors `reference/openmagnetar/pcs.py`.

use om_field::K;
use om_sumcheck::{PackedBits, VerificationError, mle_eval, mle_eval_bits};
use om_transcript::{Hasher, Transcript};

use crate::ligerito::{self as lg, LevelData, LigeritoParams, LigeritoProof};
use crate::merkle::Digest;
use crate::ring_switch::{self as rsw, RingSwitchProof};

/// A commitment: one Merkle root plus the variable count (§4.1).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Commitment {
    /// The level-0 Merkle root.
    pub root: Digest,
    /// Variables of the committed (packed) polynomial.
    pub n: usize,
}

/// Single-point MLE opening interface over K (§4.1):
/// `commit` absorbs setup (`pcs/params`, `pcs/root`) into the transcript;
/// `open`/`verify` absorb `pcs/point` and `pcs/value` first (for
/// [`BitPCS`], after the `rs/*` ring-switching steps).
pub trait Pcs {
    /// What is committed: `[K]` for [`LigeritoPCS`], `[bool]` for [`BitPCS`].
    type Input: ?Sized;
    /// Commitment type.
    type Commitment;
    /// Prover state returned by `commit`.
    type State;
    /// Opening proof type.
    type Proof;

    /// Commit, absorbing setup into `tr`.
    fn commit(&self, input: &Self::Input, tr: &mut Transcript) -> (Self::Commitment, Self::State);

    /// Verifier-side setup absorption for `cm` (no commitment computed).
    fn absorb_commitment(&self, cm: &Self::Commitment, tr: &mut Transcript);

    /// Open at `r`, returning `(y, proof)` with `y` the MLE evaluation.
    fn open(&self, state: &Self::State, r: &[K], tr: &mut Transcript) -> (K, Self::Proof);

    /// Verify an opening claim.
    ///
    /// # Errors
    /// Returns [`VerificationError`] on failure.
    fn verify(
        &self,
        cm: &Self::Commitment,
        r: &[K],
        y: K,
        proof: &Self::Proof,
        tr: &mut Transcript,
    ) -> Result<(), VerificationError>;
}

/// Ligerito PCS for a K-valued table (§4.1, §4.4).
#[derive(Clone, Debug)]
pub struct LigeritoPCS {
    /// Parameters (Python `p`).
    pub p: LigeritoParams,
    /// Hash profile (Python `h`).
    pub h: Hasher,
}

impl LigeritoPCS {
    /// With the default SHA-256 profile.
    pub fn new(params: LigeritoParams) -> Self {
        LigeritoPCS {
            p: params,
            h: Hasher::Sha256,
        }
    }

    /// With an explicit hash profile.
    pub fn with_hasher(params: LigeritoParams, hasher: Hasher) -> Self {
        LigeritoPCS {
            p: params,
            h: hasher,
        }
    }

    /// `commit(table, tr) -> (cm, state)`, absorbing setup (§4.1).
    pub fn commit(&self, table: &[K], tr: &mut Transcript) -> (Commitment, LevelData) {
        let (root, state) = lg::commit(&self.p, self.h, table);
        lg::absorb_setup(&self.p, &root, tr);
        (Commitment { root, n: self.p.n }, state)
    }

    /// Verifier-side setup absorption for `cm`.
    pub fn absorb_commitment(&self, cm: &Commitment, tr: &mut Transcript) {
        lg::absorb_setup(&self.p, &cm.root, tr);
    }

    /// `open(state, r, tr) -> (y, proof)` with `y = f̃(r)`.
    pub fn open(&self, state: &LevelData, r: &[K], tr: &mut Transcript) -> (K, LigeritoProof) {
        let y = mle_eval(&state.f, r);
        (y, lg::open_(&self.p, self.h, state, r, y, tr))
    }

    /// `verify(cm, r, y, proof, tr)`.
    ///
    /// # Errors
    /// Returns [`VerificationError`] on a size mismatch or failed check.
    pub fn verify(
        &self,
        cm: &Commitment,
        r: &[K],
        y: K,
        proof: &LigeritoProof,
        tr: &mut Transcript,
    ) -> Result<(), VerificationError> {
        if cm.n != self.p.n {
            return Err(VerificationError::new("commitment size mismatch"));
        }
        lg::verify(&self.p, self.h, &cm.root, r, y, proof, tr)
    }
}

impl Pcs for LigeritoPCS {
    type Input = [K];
    type Commitment = Commitment;
    type State = LevelData;
    type Proof = LigeritoProof;

    fn commit(&self, input: &[K], tr: &mut Transcript) -> (Commitment, LevelData) {
        LigeritoPCS::commit(self, input, tr)
    }

    fn absorb_commitment(&self, cm: &Commitment, tr: &mut Transcript) {
        LigeritoPCS::absorb_commitment(self, cm, tr);
    }

    fn open(&self, state: &LevelData, r: &[K], tr: &mut Transcript) -> (K, LigeritoProof) {
        LigeritoPCS::open(self, state, r, tr)
    }

    fn verify(
        &self,
        cm: &Commitment,
        r: &[K],
        y: K,
        proof: &LigeritoProof,
        tr: &mut Transcript,
    ) -> Result<(), VerificationError> {
        LigeritoPCS::verify(self, cm, r, y, proof, tr)
    }
}

/// Prover state of [`BitPCS`]: the packed commitment state and the bits.
pub type BitState = (LevelData, Vec<bool>);

/// Prover state of the packed [`BitPCS::commit_packed`] path: the
/// level-0 Merkle tree only ([`LevelData::strip`]ped). The bits are
/// passed again to [`BitPCS::open_packed`], which re-packs the level
/// table and re-encodes the queried columns.
pub type BitStatePacked = LevelData;
/// Proof of [`BitPCS`]: ring-switching proof and Ligerito proof.
pub type BitProof = (RingSwitchProof, LigeritoProof);

/// Bit-valued PCS (§4.1): commit to a bit vector of length `2^ℓ` (`ℓ ≥ 8`)
/// via its packing (packed `n = ℓ - 7`); open via ring switching (§4.5)
/// followed by a Ligerito opening of the packed polynomial.
#[derive(Clone, Debug)]
pub struct BitPCS {
    /// The underlying Ligerito PCS over the packed polynomial.
    pub pcs: LigeritoPCS,
}

impl BitPCS {
    /// With the default SHA-256 profile.
    pub fn new(params: LigeritoParams) -> Self {
        BitPCS {
            pcs: LigeritoPCS::new(params),
        }
    }

    /// With an explicit hash profile.
    pub fn with_hasher(params: LigeritoParams, hasher: Hasher) -> Self {
        BitPCS {
            pcs: LigeritoPCS::with_hasher(params, hasher),
        }
    }

    /// `commit(bits, tr) -> (cm, state)`: pack, then Ligerito-commit.
    pub fn commit(&self, bits: &[bool], tr: &mut Transcript) -> (Commitment, BitState) {
        let (cm, st) = self.pcs.commit(&rsw::pack(bits), tr);
        (cm, (st, bits.to_vec()))
    }

    /// Verifier-side setup absorption (delegates to the inner PCS).
    pub fn absorb_commitment(&self, cm: &Commitment, tr: &mut Transcript) {
        self.pcs.absorb_commitment(cm, tr);
    }

    /// `open(state, r, tr) -> (y, (rs_proof, ligerito_proof))`.
    ///
    /// # Panics
    /// Panics if the packed opening value disagrees with ring switching
    /// (the Python `assert yp == v`).
    /// Commit to a packed bit vector: the same commitment as
    /// [`BitPCS::commit`] on the unpacked bits, without expanding
    /// them.
    ///
    /// # Panics
    /// As [`BitPCS::commit`].
    pub fn commit_packed(
        &self,
        bits: &PackedBits,
        tr: &mut Transcript,
    ) -> (Commitment, BitStatePacked) {
        let (root, mut st) = lg::commit_owned(&self.pcs.p, self.pcs.h, rsw::pack_packed(bits));
        st.strip();
        lg::absorb_setup(&self.pcs.p, &root, tr);
        (
            Commitment {
                root,
                n: self.pcs.p.n,
            },
            st,
        )
    }

    /// The packed counterpart of [`BitPCS::open`]: same transcript
    /// and proof bytes, computed from the commitment's tree and the
    /// packed `bits` it was made from. The value `y` comes from the
    /// ring-switching partial evaluations; no table over all `2^ell`
    /// bits is built.
    ///
    /// # Panics
    /// As [`BitPCS::open`] (a packed value inconsistent with ring
    /// switching fails the first Ligerito round's check), plus if
    /// `bits` has the wrong size for the tree.
    pub fn open_packed(
        &self,
        state: BitStatePacked,
        bits: &PackedBits,
        r: &[K],
        tr: &mut Transcript,
    ) -> (K, BitProof) {
        let (rs_proof, r_s, v, y) = rsw::rs_prove_packed_value(bits, r, tr);
        // `v` is the packed polynomial's value at `r_s` (what `open`
        // asserts against `mle_eval`); a wrong `v` would fail the first
        // Ligerito sum-check round's consistency check.
        let st = state.with_f(rsw::pack_packed(bits));
        let pf = lg::open_owned(&self.pcs.p, self.pcs.h, st, &r_s, v, tr);
        (y, (rs_proof, pf))
    }

    pub fn open(&self, state: &BitState, r: &[K], tr: &mut Transcript) -> (K, BitProof) {
        let (st, bits) = state;
        let y = mle_eval_bits(bits, r);
        let (rs_proof, r_s, v) = rsw::rs_prove(bits, r, y, tr);
        let (yp, pf) = self.pcs.open(st, &r_s, tr);
        assert_eq!(yp, v, "packed opening must match the ring-switching output");
        (y, (rs_proof, pf))
    }

    /// `verify(cm, r, y, proof, tr)`: ring switching, then Ligerito.
    ///
    /// # Errors
    /// Returns [`VerificationError`] on any failed check.
    pub fn verify(
        &self,
        cm: &Commitment,
        r: &[K],
        y: K,
        proof: &BitProof,
        tr: &mut Transcript,
    ) -> Result<(), VerificationError> {
        let (rs_proof, pf) = proof;
        let (r_s, v) = rsw::rs_verify(r, y, rs_proof, tr)?;
        self.pcs.verify(cm, &r_s, v, pf, tr)
    }
}

impl Pcs for BitPCS {
    type Input = [bool];
    type Commitment = Commitment;
    type State = BitState;
    type Proof = BitProof;

    fn commit(&self, input: &[bool], tr: &mut Transcript) -> (Commitment, BitState) {
        BitPCS::commit(self, input, tr)
    }

    fn absorb_commitment(&self, cm: &Commitment, tr: &mut Transcript) {
        BitPCS::absorb_commitment(self, cm, tr);
    }

    fn open(&self, state: &BitState, r: &[K], tr: &mut Transcript) -> (K, BitProof) {
        BitPCS::open(self, state, r, tr)
    }

    fn verify(
        &self,
        cm: &Commitment,
        r: &[K],
        y: K,
        proof: &BitProof,
        tr: &mut Transcript,
    ) -> Result<(), VerificationError> {
        BitPCS::verify(self, cm, r, y, proof, tr)
    }
}
