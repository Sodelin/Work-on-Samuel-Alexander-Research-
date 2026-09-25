# Reproduction guide

The repository uses Python 3 with only the standard library for finite checks, and Lean 4.33.1 with its bundled standard library for graph proofs and rational arithmetic. The optional real-number development separately pins Mathlib; it is not required for the default core build.

## Lean

Install [elan](https://github.com/leanprover/elan) and use the root [`lean-toolchain`](lean-toolchain). From the repository root:

```sh
lake build
python checks/audit_lean.py --output verification/formal-audit.json
```

On the original Windows host, elan requires its existing directory in `ELAN_HOME` and its `bin` on `PATH`. The [default import](lean/SamuelAlexanderResearch.lean) builds the entire core library. The [current audit](verification/formal-audit.json) records endpoint counts and hashes; [FORMALIZATION.md](FORMALIZATION.md) maps claims to statements. The audit refreshes the build, verifies the pinned compiler and rejects missing reports or unexpected axioms.

## Finite checks

From the repository root:

```sh
python -m unittest discover -s checks -p 'test_*.py' -v
python checks/check_local_certificate.py
python research/thue-morse/interval_check.py
python research/thue-morse/sharp_check.py --output research/thue-morse/sharp-check-results.json
```

The six unit tests and all three diagnostic commands pass. The longer historical scans can be replayed separately when needed:

```sh
python checks/explore.py --limit 8192 --output checks/scan-8192.json
python checks/bitset_probe.py --limit 131072 --output checks/scan-bitset-131072.json.gz
```

`explore.py` computes every frontier of matching paths in the specific Thue-Morse graph, merges only equal endpoints at the same depth, and stops on the first empty frontier. Its loop is guarded by the proved quadratic bound. The independent small-case test keeps full path histories. `bitset_probe.py` uses a distinct bitset transition engine and stops at the linear budget that was conjectural when it was written; if a frontier remains at that budget, it records a counterexample lower bound instead of claiming an exact length. The saved scan found none, so its stored lengths are exact for the tested range. The historical conjectural labels in those scan artifacts record their original stage; the inequality is now proved separately and Lean checked.

`check_local_certificate.py` checks a finite truth table for distinct predecessor witnesses in two prescribed step sets. It verifies the local premise; it does not search all cellular-automaton evolutions or prove a spaceship exists.

`interval_check.py` follows the two boundary trajectories given by the proved interval theorem. It compares 8,191 stored exact lengths, 1,632 complete small frontiers including extinction, and 8,192 dyadic substitution-table cases.

`sharp_check.py` independently replays 18 complete trajectories for starts `6q-1` and `3q`, with `q=2^n` and `n=0,...,8`. It checks all 8,140 advances, the last positive offset and first zero, the exact 12 equality starts in the existing 8,192-start scan, and 256 bounded baseline first-hit times. It does not run a new path scan. Its output is explicitly finite corroboration. The universal bound and exact equality set are established by the [constructive proof](research/thue-morse/NEXT-INVARIANT.md) and [Lean sharp theorem](lean/SamuelAlexanderResearch/SharpThueMorse.lean); the full `H(v)` first-hit formula and real-coefficient optimality now have separate checked endpoints in SharpCorollaries and RealBridges.

The workflow runs the core and pinned real-project audits, tests and finite diagnostics. Historical long scans are not rerun on every push. The positive binary theorem, enumeration and infinite critical conservation are now encoded; the remaining research and model boundaries are listed in [FORMALIZATION.md](FORMALIZATION.md).


## Optional real-number project

Follow [the exact pinned setup](notes/REAL-BRIDGES-FORMALIZATION.md), then run
`python checks/audit_lean.py --real --output verification/real-audit.json`.
This separately builds and audits real birthdate transport, real coefficient
optimality and real convex-hull inclusion. It verifies the Mathlib commit.

## Full-height conjecture diagnostics

`python research/thue-morse/kernel_conjecture_check.py --output research/thue-morse/kernel-conjecture-results.json`
checks the proposed complete height formula against stored exact values,
candidate coordinate identities and fresh actual frontier computations.
Cases exceeding its explicit advance cap are listed as skipped. A passing
run does not establish the conjecture.
