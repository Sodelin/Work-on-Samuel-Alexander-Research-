# Degree formalization scope

The initial revision checked only arithmetic consequences of the edge-count inequality in `DegreeBounds.lean`. That module remains available, but its earlier scope limitation has now been closed by [PopulationCounting.lean](../lean/SamuelAlexanderResearch/PopulationCounting.lean).

The new module defines actual labelled adjacency, finite edge sums, distinct-label parent coverage, permanent vertex genders, root flags, and child caps. It proves the double count rather than assuming it. It also constructs predecessor-closed prefixes and proves the infinite subcritical contradiction from a single naturally ordered infinite graph with finitely supported roots and children.

The development uses explicit finite sums in `Std`, so no Mathlib installation was needed. The earlier attempt's unavailable `Finset`/`Fintype` tools were a limitation of that approach, not an obstruction to formalization.

The later extensions and remaining boundary are explicit:

- BirthOrder and PopulationReindex now construct the natural presentation; RealBridges specializes it to actual real dates.
- PopulationCounting's identity uses a finite ambient graph. InfiniteConservation now proves the full infinite identity, triangular budget and eventual regularity separately.
- The two-child fixed-gender avoidance question is a separate mathematical problem and remains unresolved.

See the [detailed counting note](POPULATION-COUNTING-FORMALIZATION.md), [central coverage table](../FORMALIZATION.md), and [integrated verification receipt](../verification/FORMALIZATION-RECEIPT.md). Reproduce with `lake build` and `python checks/audit_lean.py` from the repository root.
