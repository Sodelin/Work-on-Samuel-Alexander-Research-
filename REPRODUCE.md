# Reproduction guide

The repository uses Python 3 with only the standard library for finite checks, and Lean 4.33.1 with its bundled `Std` library for the current arithmetic module. No Mathlib download is required for the present Lean code.

## Lean

Install [elan](https://github.com/leanprover/elan) and use the root [`lean-toolchain`](lean-toolchain). From the repository root:

```sh
lake build
```

On the original Windows host, elan required `ELAN_HOME` to be set to the existing elan directory before invoking `lake`. The recorded build used Lean 4.33.1 and finished successfully. The formal theorem statements are in [`lean/SamuelAlexanderResearch/DegreeBounds.lean`](lean/SamuelAlexanderResearch/DegreeBounds.lean); the graph-to-edge-count implication is a prose step as documented in [FORMALIZATION-SCOPE.md](notes/FORMALIZATION-SCOPE.md).

## Finite checks

From the repository root:

```sh
python -m unittest discover -s checks -p 'test_*.py' -v
python checks/check_local_certificate.py
python checks/explore.py --limit 8192 --output checks/scan-8192.json
python checks/bitset_probe.py --limit 131072 --output checks/scan-bitset-131072.json.gz
```

`explore.py` computes every frontier of matching paths in the specific Thue–Morse graph, merges only equal endpoints at the same depth, and stops on the first empty frontier. Its loop is guarded by the proved quadratic bound. The independent small-case test keeps full path histories. `bitset_probe.py` uses a distinct bitset transition engine and stops at the proposed linear budget; if a frontier remains at that budget, it records a counterexample lower bound instead of claiming an exact length. The saved scan found none, so its stored lengths are exact for the tested range. Both JSON files label the linear inequality conjectural.

`check_local_certificate.py` checks a finite truth table for distinct predecessor witnesses in two prescribed step sets. It verifies the local premise; it does not search all cellular-automaton evolutions or prove a spaceship exists.

The GitHub workflow runs the Lean build, the Python tests, and the toy local-rule example. It does not run the long finite scans on every push; they can be replayed with the commands above.
