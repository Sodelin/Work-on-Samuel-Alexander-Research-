# Integrated formalization receipt

Checked locally on 24 September 2026 (25 September UTC). The final endpoint audit is timestamped `2026-09-25T04:49:28.087647+00:00` and identifies the exact final sources by SHA-256. This receipt describes local execution; the pull request's CI result is recorded separately once observed. It supersedes the earlier eight-module, 52-endpoint integration stage.

| Check | Observed result |
|---|---|
| `lake build` | Success; all eleven modules and the default root import build together. |
| `python checks/audit_lean.py --output verification/formal-audit.json` | Pass, all 80 selected endpoints. All dependencies are subsets of `propext`, `Classical.choice`, `Quot.sound`. |
| `python -m unittest discover -s checks -p 'test_*.py' -v` | Six tests passed. |
| `python checks/check_local_certificate.py` | `Toy rule certificate: (True, 3, None)`. |
| `python research/thue-morse/interval_check.py` | 8,191 exact lengths agreed with stored set-frontier results; 1,632 complete-frontier states agreed with direct edge expansion; 8,192 dyadic-table cases agreed. |
| `python research/thue-morse/sharp_check.py --output research/thue-morse/sharp-check-results.json` | Pass: 18 complete trajectories, 8,140 advances, descent-entry and extinction-index checks, 256 bounded `H(v)` first-hit checks, and the exact inequality/equality set in the existing 8,192-start scan. |
| Source placeholder scan | No `sorry`, `admit`, `native_decide`, or project `axiom` declarations in the Lean sources. |

Toolchain: `leanprover/lean4:v4.33.1`, compiler commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, Windows GNU release build. Python checks use only the standard library. No long 131,071-start scan was rerun for this patch.

The final checked sharp theorem includes the actual Thue-Morse sequence,
all dyadic run calculations, the interval-to-original-edge bridge, the
universal path-length bound, existence of finite maxima, the equality
family, and the exact equality classification. The universal
`RootObstruction.population_root_obstruction` theorem is also included:
every binary natural-date population has distinct roots `0` and `1` and
its whole graph fails common ancestry. The exact full `H(v)` first-hit
formula and real-coefficient optimality are prose corollaries, not
separately exported endpoints.

On the original Windows host the commands used `ELAN_HOME=C:\Users\Owner\.elan` and added its `bin` directory to the command's `PATH`. These are process-local environment settings; no global toolchain configuration was changed.

The [JSON receipt](formal-audit.json) contains exact final source hashes and the report for each audited endpoint. The [statement review](STATEMENT-REVIEW.md) and [central coverage report](../FORMALIZATION.md) must accompany this receipt: clean axiom dependencies do not erase the explicit positive-classification premise, the missing real-date enumeration bridge, or the remaining infinite critical-conservation development. Alexander's Example 14(1) retains attribution for the related root-cone phenomenon; this receipt establishes no literature-priority claim. Historical receipts certify their original stages, not the final tree recorded here.
