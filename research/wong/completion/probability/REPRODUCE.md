# Reproduce the probability candidate at pinned dependencies

Use a clean checkout of the publisher's exact candidate commit. The three
new modules, updated `real/RealAudit.lean`, and updated `real/lakefile.lean`
must match the release manifest. This page describes a future verification
run; it is not evidence that the run has happened.

Lean is `leanprover/lean4:v4.33.1`; Mathlib is `0df444a360eaa60ab8c11dca51a86af692955474`.
The root and real-project toolchain pins must agree. The existing strict
`checks/audit_lean.py` is unchanged and checks both pins, builds the library,
checks every registered report, and rejects axioms outside `propext`,
`Classical.choice`, and `Quot.sound`.

From the repository root in the hosted Linux environment, run:

```bash
cd real
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
lake env lean --version
test "$(git -C .lake/packages/mathlib rev-parse HEAD)" = "0df444a360eaa60ab8c11dca51a86af692955474"
lake exe cache get Mathlib.Order.Zorn Mathlib.Data.Finset.Card Mathlib.Logic.Encodable.Basic Mathlib.SetTheory.Ordinal.Rank Mathlib.Order.WellFounded Mathlib.Data.Finset.Lattice.Fold Mathlib.Algebra.Order.Archimedean.Real.Basic Mathlib.Algebra.Order.Archimedean.Basic Mathlib.Analysis.Convex.Hull Mathlib.Tactic.Linarith Mathlib.Tactic.Positivity Mathlib.Tactic.NormNum Mathlib.Tactic.Ring Mathlib.Data.Fintype.EquivFin Mathlib.Data.Finset.Union Mathlib.Data.Finset.Max Mathlib.Data.Finset.Prod Mathlib.Data.Fintype.Prod Mathlib.Algebra.BigOperators.Fin Mathlib.Tactic.FieldSimp Mathlib.Tactic.FinCases Mathlib.Data.Finset.Filter Mathlib.Data.Real.Basic Mathlib.Algebra.BigOperators.Ring.Finset Mathlib.Algebra.Order.BigOperators.Group.Finset Mathlib.Data.Fintype.BigOperators Mathlib.Data.List.Sort Mathlib.Algebra.BigOperators.Group.Finset.Basic Mathlib.MeasureTheory.OuterMeasure.BorelCantelli Mathlib.Probability.Kernel.IonescuTulcea.Traj Mathlib.Topology.Algebra.InfiniteSum.ENNReal
cd ..
python3 checks/audit_lean.py --real --output verification/real-audit.json
```

The existing hosted audit command omits `--output`; it performs the same
checks and prints the count. Supplying `--output` only preserves the actual
receipt after success. It must never be used to prefill a candidate receipt.
Run all the repository's other existing CI checks as well; this packet does
not weaken, replace, or bypass them.

The cache command above preserves the observed public workflow's existing
roots and appends only the four direct imports needed by the new modules.
The separately delivered `CACHE-COMMAND-DELTA.patch` was checked against
workflow bytes at `024ef6f25ed168e36a26d2a8c855d8bd7825b336`, identical to `46aac52e214311fb2c2230b1b4fe37c42ef9e1a9`.
If the publisher has added roots since that observation, merge the four new
imports into the current line while preserving those later additions.

## Acceptance and records

A pass requires an exit-zero strict audit with exactly **293 unique selected
endpoints**. The previous 274 endpoint names must remain and the only new
selected names must be the 19 in [SOURCE-MANIFEST.json](SOURCE-MANIFEST.json).
The three source hashes must match that manifest, and the audit must use the
pinned dependency source. A new receipt, if captured, must name 293 endpoints
and bind these actual source bytes. Warnings stay visible in the build logs;
they must not conceal a missing endpoint or forbidden axiom.

The publisher records the candidate commit, hosted run URL and conclusion.
Only after the full hosted run succeeds may integration be described as
verified. Until then the prior 274 receipt keeps its prior scope. Core and
standalone audit counts are separate inventories; the probability packet
adds no standalone registrations.

## Historical local evidence

The [candidate status](CANDIDATE-STATUS.md) describes the donor cache
provenance gap. [SOURCE-MANIFEST.json](SOURCE-MANIFEST.json) binds the original
worker's three sources and logs; [REVIEW-MANIFEST.json](REVIEW-MANIFEST.json)
binds the original manual review snapshot. Those artifacts are unchanged.
The machine-specific [local runner](local-attempt/audit_293.py) and its
[attempt record](local-attempt/ATTEMPT-STATUS.json) document the incomplete
retry, not the portable admission command. No `.olean` binaries or downloaded
dependency artifacts are included in this publication packet.
