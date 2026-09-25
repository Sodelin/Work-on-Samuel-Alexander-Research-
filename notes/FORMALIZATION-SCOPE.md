# Finite-graph Lean attempt and stopping point

The requested end-to-end target is a theorem for a finite directed graph on a birthdate-ordered prefix: every nonroot has one distinct incoming parent per label, every vertex has at most `d` children, and therefore `(k - d) * N <= k * R_N`.

The existing `DegreeBounds.lean` checks the final arithmetic from `k * (N - R_N) <= d * N`. It does **not** define the graph, count its edges, or prove that inequality from parent and child hypotheses.

I attempted a standalone Lean 4.33.1 implementation using `import Std`, then probed for the finite-set/cardinality tools needed for the two edge counts. In this installed standard library, `Finset` and `Fintype` are unavailable (`unknown identifier`). I also tried to compile with `import Mathlib` directly and through the locally available `new-math-discovery` Lake environment; both reported `unknown module prefix 'Mathlib'`. That repository's `.lake` directory did not contain a mathlib package. Rebuilding this counting infrastructure from `List` or fetching/building Mathlib would exceed this bounded lane.

Consequently the finite-graph implication is still a **prose proof**, while the arithmetic implication is **Lean checked**. No claim of an end-to-end Lean theorem is made. A future formalization could use a pinned Mathlib project with finite vertex type, edge relation and label function, then compare the cardinality of the same finite edge set by target and source using `Finset.sum_comm` or `Finset.card_biUnion` with disjoint fibers.

Reproduction command from the root of this repository:

```powershell
$env:ELAN_HOME='<your elan directory>'
lake build
```

This succeeds with Lean 4.33.1 and exit code 0. The exact statements are in `lean/SamuelAlexanderResearch/DegreeBounds.lean`.
