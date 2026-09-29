# Deterministic 65-endpoint release evidence

The local combined audit passed after freshly rebuilding all 61 imported local
modules. It printed exactly 274 selected reports, allowing only `propext`,
`Classical.choice`, and `Quot.sound`. This is an extension of the public
209-endpoint real development, which also contains other research.

The input sources match the immutable [input manifest](INPUT-MANIFEST.json).
The [aggregate receipt](combined-real-audit.json) records source hashes,
compiler identity, all selected axiom dependencies, module rebuild times and
log hashes. The [aggregate log](RealAudit.txt) preserves the actual reports.
The three new module logs and their historical isolated receipts are retained
alongside it. Historical file paths describe the original checking machine;
they are provenance, not portable command paths.

The [independent review](SOL2-REVIEW.md) is a bounded statement/source review
with counterexample attempts. It did not run another Lean kernel. It accepted
the contracts with their stated limitations, including the Appendix E
`SampleSupported` restriction. [Fifteen finite controls](evidence/finite-controls.json)
separately reject tempting overgeneralizations; they are finite tests, not
substitutes for the general Lean theorems.

## Reproduce in the complete public repository

Install the repository-pinned Lean toolchain and Python. Follow the existing
real-project dependency/cache setup in `.github/workflows/verify.yml`, including
`Mathlib.Data.List.Sort`, then run from the repository root:

```sh
python3 checks/audit_lean.py --real --output verification/real-audit.json
python3 research/wong/completion/verification/deterministic65/controls.py
```

The first command invokes `lake build`, refreshes local imports, checks the
pinned Mathlib revision and audits all registered real endpoints. The second
replays the finite controls and writes their dated local receipt. Future
repository additions may increase the aggregate count; the exact 274 count
belongs to this staged source manifest. A complete checkout is required: the
publication packet contains changed files, not all dependencies.

The Windows isolation runner is a local integration harness with explicit
machine paths; the portable repository auditor above is the maintained public
verification route. No Python test establishes stochastic correctness or
whole-paper completion. Hosted CI must be attached to the exact published
commit separately.
