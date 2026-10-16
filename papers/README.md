# Source papers for the §13.9 audit

ePrint serves abstract pages to automated fetches but blocks PDF downloads
behind a Cloudflare challenge (verified 2026-10-16: direct PDF requests
return a "Just a moment..." HTML page to `curl`). The ePrint and ECCC PDFs
below were therefore fetched from the Wayback Machine (`id_` raw captures,
for example `https://web.archive.org/web/2026id_/https://eprint.iacr.org/2024/504.pdf`).
Each was checked to be a PDF of the right paper (title page and authors).
Where the archive holds several revisions, the newest was taken. The file
listed for a revision was the one checked.

Status (all obtained; every §13.9 item is resolved):

| File | Paper | Revision and source | Used for |
|---|---|---|---|
| `ligerito-2025-1187.pdf` | Novakovic–Angeris, *Ligerito*, ePrint 2025/1187 | From the first author's page, `angeris.github.io/papers/ligerito.pdf` (2026-10-16). | §13.9(1): `t` derivation, claim form, query batching. |
| `ring-switching-2024-504.pdf` | Diamond–Posen, *Polylogarithmic Proofs for Multilinears over Binary Towers*, ePrint 2024/504 | 2025-09 revision (50 pages, PDF dated 2025-09-22), Wayback capture 2026-04-20. Ring switching is §3 (Construction 3.1, Theorem 3.5, Remark 3.4). | §13.9(2). |
| `ring-switching-2024-504-rev2024-07.pdf` | the same paper | Older 2024-07 revision (37 pages, PDF dated 2024-07-17), Wayback 2024 capture. Ring switching is §4 there, without batching; proximity gaps are Theorems 2.2–2.4. | §13.9(1): Theorem 2.3 is the interleaved form of Lemma A. §13.9(2): revision note. |
| `twist-shout-2025-105.pdf` | Setty–Thaler, *Twist and Shout*, ePrint 2025/105 | February 2025 revision (96 pages, PDF dated 2025-02-27). The Wayback captures of 2025-05-22, 2026-04-30 and 2026-06-08 are byte-identical, so this is what ePrint served through mid-2026. It lists only Setty and Thaler as authors. The CRYPTO 2026 version cited as [55] (Setty–Thaler–Zhu) was not obtained. | §13.9(3). |
| `bciks-2020-654.pdf` | Ben-Sasson–Carmon–Ishai–Kopparty–Saraf, *Proximity Gaps for Reed–Solomon Codes*, ePrint 2020/654 | Revision of 3 July 2021 (61 pages), Wayback capture 2026-04-18. | §13.9(1): Theorem 4.1 (unique-decoding gap, `n/q`) is Lemma A for one row pair. |
| `bchks-eccc-tr25-169.pdf` | Ben-Sasson–Carmon–Haböck–Kopparty–Saraf, *On Proximity Gaps for Reed–Solomon Codes*, ECCC TR25-169 ([5]) | Version dated 7 November 2025 (49 pages), Wayback capture 2026-01-14 of `eccc.weizmann.ac.il/report/2025/169/download/` (the newest capture). | §13.9(1): citation correction; §13.5 option 1 (Theorem 1.3, Corollary 1.4). |

The Magnetar paper itself is already in the repo root as `paper.pdf`
(gitignored). PDFs in this directory are gitignored too; only this README is
tracked.
