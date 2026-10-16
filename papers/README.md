# Source papers needed for the §13.9 audit

ePrint serves abstract pages to automated fetches but blocks PDF downloads
behind a Cloudflare challenge (verified 2026-10-16: direct PDF requests
return a "Just a moment..." HTML page to `curl`).

Status:

| File | Paper | Status |
|---|---|---|
| `ligerito-2025-1187.pdf` | Novakovic–Angeris, *Ligerito*, ePrint 2025/1187 | Obtained 2026-10-16 from the first author's page, `angeris.github.io/papers/ligerito.pdf`. The `t` derivation in §13.9(1) has been compared. The claim form and query batching comparison is still open. |
| `ring-switching-2024-504.pdf` | Diamond–Posen, ePrint 2024/504 | Still needed for §13.9(2). Please download in a browser and drop it here with this filename. |
| `twist-shout-2025-105.pdf` | Setty–Thaler–Zhu, *Twist and Shout*, ePrint 2025/105 (CRYPTO 2026) | Still needed for §13.9(3). Please download in a browser and drop it here with this filename. Only the abstract page is reachable to automated fetches. |

Also useful if easy (for the proximity-gap citation in §13.9(1)):

| File | Paper |
|---|---|
| `bchks-proximity-gap.pdf` | BCHKS correlated-agreement / proximity-gap source cited as [5] in 04, and/or ECCC TR25-169 |

Checked again 2026-10-16: this directory and the user's Downloads folder
contain no copies of the ring-switching or Twist-and-Shout papers, and
automated downloads (direct, browser user agent, reader proxy, Semantic
Scholar) all fail. Items 13.9(2) and 13.9(3) therefore remain open until
the two PDFs are dropped in here by hand.

The Magnetar paper itself is already in the repo root as `paper.pdf`
(gitignored). PDFs in this directory are gitignored too; only this README is
tracked.
