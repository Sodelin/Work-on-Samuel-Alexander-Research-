# Faster proof feedback without changing final verification

The installed Lean 4.33.1 provides native incremental snapshots. A bounded local benchmark on `GeneralRigidity` measured 5.009 seconds for a fresh check, 8.565 seconds to create a snapshot, 1.077 seconds for unchanged reuse, and 1.132 seconds for a valid appended theorem. A deliberately false appended theorem was rejected in 0.994 seconds. These are local timings for one file, not a general speed or token-cost guarantee.

Run from the repository root:

```text
python checks/lean_feedback.py lean/SamuelAlexanderResearch/YourModule.lean --refresh
python checks/lean_feedback.py lean/SamuelAlexanderResearch/YourModule.lean
```

Refresh after a useful successful milestone, then reuse while changing later proofs. The helper builds imported project modules first and fingerprints the project pins and transitive local dependency sources/compiled artifacts. A changed dependency disables reuse. Raw output and actual exit codes are preserved under `.lake/lean-feedback`; the JSON response includes the log path and diagnostics. Each agent uses its own module and therefore its own snapshot.

This is development feedback. Final `checks/audit_lean.py`, direct axiom reports, source hashes, and hosted CI continue to run without snapshot flags. The snapshot mechanism is explicitly experimental in the [Lean release documentation](https://lean-lang.org/doc/reference/latest/releases/v4.32.0/#experimental-incremental-compilation-caching). No compiler/toolchain upgrade or additional model service was installed.

`checks/benchmark_feedback.py` reproduces the isolated five-case experiment under `.lake/feedback-benchmark`. It edits only its probe copy, including the intentional false theorem, and leaves mathematical source files unchanged.
