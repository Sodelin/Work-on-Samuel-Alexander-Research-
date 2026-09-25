# First GitHub Actions verification

The [Verify run #1](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/actions/runs/36091360866) completed successfully on the public repository for commit `ff010210ba61e2db13295e3ee2cae050bb690c0c` (25 September 2026, UTC). Its `lean-and-python` job reported success for checkout, `leanprover/lean-action@v1`, six Python tests, and the local-rule example. This receipt was read from GitHub after the push; it is separate from the local verification record.

The successful build checks the exact arithmetic Lean module in that commit. It does not formalize Alexander's complete graph axioms, prove the Thue–Morse linear conjecture, or independently replay the long scans. Consult [STATUS.md](../STATUS.md) and the [local receipt](LOCAL-RECEIPT.md) for those boundaries.
