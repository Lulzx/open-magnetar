//! Port of `reference/tests/test_merkle.py`.

use om_pcs::merkle::{MerkleTree, hash_leaf, hash_node, verify_multi};
use om_transcript::Hasher;

fn leaves(n: usize) -> Vec<Vec<u8>> {
    (0..n).map(|i| vec![i as u8; i % 5 + 1]).collect()
}

const H: Hasher = Hasher::Sha256;

#[test]
fn single_leaf() {
    let l = leaves(1);
    let t = MerkleTree::new(H, &l);
    assert_eq!(t.root(), hash_leaf(H, &l[0]));
    verify_multi(H, &t.root(), 1, &[0], &l, &t.open(&[0]).unwrap()).unwrap();
}

#[test]
fn two_leaves_formula() {
    let l = leaves(2);
    let t = MerkleTree::new(H, &l);
    assert_eq!(
        t.root(),
        hash_node(H, &hash_leaf(H, &l[0]), &hash_leaf(H, &l[1]))
    );
}

#[test]
fn multi_open_all_sizes() {
    for n in [1usize, 2, 3, 5, 8, 11, 16] {
        let l = leaves(n);
        let t = MerkleTree::new(H, &l);
        let mut cases: Vec<Vec<usize>> = vec![
            vec![0],
            vec![n - 1],
            (0..n).step_by(2).collect(),
            (0..n).collect(),
            if n > 1 { vec![0, n - 1] } else { vec![0] },
        ];
        for idx in &mut cases {
            idx.sort_unstable();
            idx.dedup();
            let auth = t.open(idx).unwrap();
            let opened: Vec<Vec<u8>> = idx.iter().map(|&i| l[i].clone()).collect();
            verify_multi(H, &t.root(), n, idx, &opened, &auth).unwrap();
        }
    }
}

#[test]
fn dedup_full_set_needs_no_auth() {
    let t = MerkleTree::new(H, &leaves(8));
    assert_eq!(
        t.open(&(0..8).collect::<Vec<_>>()).unwrap(),
        Vec::<Vec<u8>>::new()
    );
}

#[test]
fn tamper() {
    let l = leaves(8);
    let t = MerkleTree::new(H, &l);
    let idx = [1usize, 2, 6];
    let auth = t.open(&idx).unwrap();
    let good: Vec<Vec<u8>> = idx.iter().map(|&i| l[i].clone()).collect();

    let mut bad_leaf = good.clone();
    bad_leaf[0].push(b'x');
    assert!(verify_multi(H, &t.root(), 8, &idx, &bad_leaf, &auth).is_err());

    for j in 0..auth.len() {
        let mut a = auth.clone();
        a[j][0] ^= 1;
        assert!(
            verify_multi(H, &t.root(), 8, &idx, &good, &a).is_err(),
            "auth {j}"
        );
    }
    assert!(verify_multi(H, &t.root(), 8, &idx, &good, &auth[..auth.len() - 1]).is_err());
    let mut long = auth.clone();
    long.push(auth[0].clone());
    assert!(verify_multi(H, &t.root(), 8, &idx, &good, &long).is_err());
    // not ascending / wrong index / empty / out of range
    assert!(verify_multi(H, &t.root(), 8, &[2, 1, 6], &good, &auth).is_err());
    assert!(verify_multi(H, &t.root(), 8, &[1, 2, 7], &good, &auth).is_err());
    assert!(verify_multi(H, &t.root(), 8, &[], &[], &auth).is_err());
    assert!(verify_multi(H, &t.root(), 8, &[8], &good[..1], &auth).is_err());
    assert!(t.open(&[]).is_err());
    assert!(t.open(&[1, 1]).is_err());
}

#[test]
fn domain_separation() {
    let (a, b) = (hash_leaf(H, b"a"), hash_leaf(H, b"b"));
    let mut ab = a.clone();
    ab.extend_from_slice(&b);
    assert_ne!(hash_leaf(H, &ab), hash_node(H, &a, &b));
}

#[test]
fn sha3_profile() {
    let h = Hasher::Sha3_256;
    let l = leaves(6);
    let t = MerkleTree::new(h, &l);
    verify_multi(h, &t.root(), 6, &[3], &l[3..4], &t.open(&[3]).unwrap()).unwrap();
}

#[test]
fn sha384_profile_48_byte_digests() {
    let h = Hasher::Sha384;
    let l = leaves(5);
    let t = MerkleTree::new(h, &l);
    assert_eq!(t.root().len(), 48);
    let idx = [1usize, 4];
    let opened: Vec<Vec<u8>> = idx.iter().map(|&i| l[i].clone()).collect();
    verify_multi(h, &t.root(), 5, &idx, &opened, &t.open(&idx).unwrap()).unwrap();
}
