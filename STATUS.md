# Verification status

Status recorded for the initial repository package, 24 September 2026. "Lean checked" below refers to a successful local Lean 4.33.1 build of the exact repository module. It does not describe a complete formalization of the cited papers.

| Claim | Written argument | Finite check | Lean coverage | Remaining gate |
|---|---|---|---|---|
| Alexander's eventual-periodic unavoidability theorem | Prior result in ALEX13 | None here | None here | Use the cited published result; do not reattribute it. |
| Classification by eventual periodicity | Prior result in CLASS26 | Original repo has its own controls | Original repo reports a Lean endpoint for the negative direction; this repository has not rebuilt it | Independent audit of the original formal statement and full literature priority, if making a publication claim. |
| Thue–Morse quadratic path-length upper bound | Proved in [note](notes/THUE-MORSE-PATHS.md), conditional on the classical overlap-free theorem | Exact BFS agrees on checked cases and stays below the bound | None | Independent proof review; formalize overlap-freeness and path bound if full Lean coverage is desired. |
| Proposed linear bound and equality family | No proof | Set-frontier starts `0..8191`; bitset-transition starts `1..131071`; no counterexamples in claimed ranges and all shared lengths agree | None | Proof or counterexample. |
| Offspring threshold and binary gender balance | Proved by edge counts in [note](notes/DEGREE-BOUNDARY.md) | No computation needed | [Arithmetic consequences](lean/SamuelAlexanderResearch/DegreeBounds.lean) compile from count premises | Formalize finite graph, edge counts, and birthdate prefix assumptions for an end-to-end Lean theorem. |
| Two-child fixed-gender avoidance for all aperiodic binary sequences | No result | No systematic scan | None | Construction or impossibility theorem; prior-art review. |
| Periodic lifeline certificate and velocity polygon | Proved as a conditional reduction in [note](notes/PERIODIC-LIFELINE.md) | Generic finite checker passes a toy valid rule and rejects a one-parent negative case | None | Independent mathematical review; a specific useful new speed application. |
| Automatic-sequence universality decision | Direct corollary from two cited results | No implementation | None | An explicit algorithm and formalization only if this line is pursued. |

## Local checks performed

- Lean 4.33.1: `lake build` completed for `SamuelAlexanderResearch.DegreeBounds` and the top-level module. The `.lean` file contains no `sorry`; its graph-count premise is explicit.
- Python: `python -m unittest discover -s checks -p 'test_*.py' -v` passed 6 tests.
- Local-rule toy: `python checks/check_local_certificate.py` printed `Toy rule certificate: (True, 3, None)`.
- Thue–Morse scans: saved JSON reports cover starts `0..8191` and `1..131071`, using different frontier transitions. Their absence of linear-bound counterexamples is finite evidence only.

These are local results. The [first GitHub Actions run](verification/CI-RECEIPT.md) also succeeded for commit `ff010210ba61e2db13295e3ee2cae050bb690c0c`; it built Lean and ran the small Python checks. Remote CI does not run either long finite scan or prove the unformalized propositions.
