# Source papers needed for the §13.9 audit

ePrint serves abstract pages to automated fetches but blocks PDF downloads
behind a Cloudflare challenge (verified 2026-10-16: the three PDFs below
return a "Just a moment..." HTML page to `curl`). Please download these PDFs
in a browser and drop them in this directory with these filenames:

| File | Paper | Needed for |
|---|---|---|
| `ligerito-2025-1187.pdf` | Novakovic–Angeris, *Ligerito*, ePrint 2025/1187 | §13.9(1): claim form, query batching, `t` derivation, tensor-fold gap |
| `ring-switching-2024-504.pdf` | Diamond–Posen, ePrint 2024/504 | §13.9(2): ring switching for `β_j = X^j`, `7/|K|` term |
| `twist-shout-2025-105.pdf` | Setty–Thaler–Zhu, *Twist and Shout*, ePrint 2025/105 (CRYPTO 2026) | §13.9(3)–(5): Twist/Shout prover algorithms, one-hot check |

Also useful if easy (for the proximity-gap citation in §13.9(1)):

| File | Paper |
|---|---|
| `bchks-proximity-gap.pdf` | BCHKS correlated-agreement / proximity-gap source cited as [5] in 04, and/or ECCC TR25-169 |

The Magnetar paper itself is already in the repo root as `paper.pdf`
(gitignored). PDFs in this directory are gitignored too; only this README is
tracked.
