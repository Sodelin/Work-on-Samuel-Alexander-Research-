# Integrated formalization receipt

This receipt records the completed local gap-closure pass. The core audit ran
at `2026-09-25T06:34:15.813834+00:00` and the real audit at
`2026-09-25T06:35:10.693788+00:00`. Their machine-readable receipts identify every
audited source by SHA-256. This supersedes the earlier eleven-module,
80-endpoint integration receipt; older commit-specific receipts remain historical.

| Check | Observed result |
|---|---|
| Core build and audit | All 33 core modules and the aggregate import build; all 275 selected endpoints pass. |
| Optional real project | All 19 selected endpoints pass with Mathlib pinned to `0df444a360eaa60ab8c11dca51a86af692955474`. |
| Proof dependencies | Every audited endpoint uses only subsets of `propext`, `Classical.choice`, `Quot.sound`. |
| Source placeholder scan | No `sorry`, `admit`, `native_decide` or project axiom declarations. |
| Finite-path unit tests | Six tests pass. |
| Toy local certificate | `Toy rule certificate: (True, 3, None)`. |
| Exact interval diagnostic | 8,191 stored length agreements, 1,632 direct-frontier agreements, 8,192 paired-table checks. |
| Sharp trajectory diagnostic | 18 complete trajectories, 8,140 advances, 256 first-hit checks and the stored inequality/equality family pass. |
| New conjecture diagnostic | 131,071 stored positive lengths plus start zero, 16,384 complete coordinate transitions, and 2,200 fresh actual frontier computations agree. Fourteen deliberately long cases reach the cap and are skipped. This does not prove the conjecture. |
| Documentation integrity | Exactly ten numbered proposals; every local Markdown target exists. |

Compiler: `Lean (version 4.33.1, x86_64-w64-windows-gnu, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)`. Python diagnostics use the standard
library. The default proof library remains Std-only. The optional real project
is separate and uses the same Lean version. Windows cache recovery preserved
TLS certificate verification and used the ordinary Mathlib unpacker.

The [core receipt](formal-audit.json), [real receipt](real-audit.json),
[statement review](GAP-CLOSURE-REVIEW.md), and [coverage report](../FORMALIZATION.md)
belong together. Proof dependencies do not by themselves establish statement
fidelity, significance or novelty. Independent reviews checked the actual
population, retained-subtype and shifted-graph models.

Two files had only CRLF-to-LF normalization after their independent review:
InfiniteConservation and QuantitativeAvoidance. Their non-newline bytes were
unchanged, the final normalized files were rebuilt, and these receipts hash
the bytes that are published. The selected proof hashes are also checked
against Git's index before publication.

This is local execution evidence. Hosted Linux CI must be observed on the
published commit separately; previous CI results do not certify this tree.
The [workflow](../.github/workflows/verify.yml) runs both projects' audits and
the established finite diagnostics. No long 131,071-start scan was rerun;
the new conjecture check reuses its stored exact values and independently
computes the stated fresh cases.
