# Arbitrary-presentation degree and root transport

[`PopulationReindex.lean`](../lean/SamuelAlexanderResearch/PopulationReindex.lean) constructs a naturally indexed labelled population from an infinite original vertex type with locally finite ordered birth times. It transports the existing subcritical impossibility theorem and the initial-root theorem back to the original vertices. Neither an enumeration nor an aggregate degree inequality is supplied as an input.

The main consequences are `subcritical_impossible`, which rules out a child cap $`d < k`$, and `at_least_k_distinct_roots`, which produces an injective family of actual original roots indexed by `Fin k`. The theorem `alphabet_le_root_cover_length` also proves that every finite list covering the original root set has at least $`k`$ entries.

## Exact input model

`PresentedPopulation birth k d` uses arbitrary types $`V`$ of vertices and `Time` of birth times. Its local assumptions are:

- `InfiniteVertices V`: every finite list of vertices omits some vertex.
- `FiniteSublevels birth`: for every time $`r`$, a finite list covers all vertices $`x`$ with $`\operatorname{birth}(x)\le r`$.
- A functional edge map `edge : V -> V -> Option Nat`. `none` means no edge; `some label` means one edge with that label, and every label is less than $`k`$.
- Every actual edge strictly increases birth time.
- A finite list covers the actual roots, defined by `NoParents edge x := forall parent, edge parent x = none`.
- At every vertex that is not an actual root, each label below $`k`$ occurs on an incoming edge.
- At each vertex, some finite list of length at most $`d`$ covers every actual child.

The construction requires the Std order instances `IsLinearPreorder Time` and `LawfulOrderLT Time`, in addition to `LE Time` and `LT Time`. Equal birth times are allowed; finite closed sublevels also bound the number of vertices tied at any time. Edges must have strictly increasing times, so their enumeration indices increase strictly even when other vertices have tied dates.

The child-cover list may contain duplicate entries or vertices that are not children. Its length must still be at most $`d`$, and it must cover all children in the original graph, including those beyond any particular initial segment. The root cover likewise may contain extra vertices. No Boolean root marker, precomputed support bound, or count inequality is assumed in the original presentation.

## Checked construction and endpoints

All names below are in namespace `PopulationReindex`.

| Endpoint | Checked content |
| --- | --- |
| `enumeration` | Constructs a birth-ordered bijection `Nat -> V` using `BirthOrder.orderedEnumeration` from infinitude and finite sublevels. |
| `indexedEdge` | Pulls the original edge map back through the constructed enumeration, preserving its exact `Option Nat` value. |
| `indexedRoot_true_iff`, `indexedRoot_false_iff` | The constructed Boolean root marker agrees with actual original parentlessness and its negation. |
| `indexedRoot_noParents_iff` | The marker is true exactly when the vertex has no parent in the reindexed graph. Surjectivity covers every possible original parent. |
| `indexed_birth_order` | Every reindexed edge increases its natural index strictly. |
| `indexed_label_valid` | Reindexing preserves the condition that edge labels are below $`k`$. |
| `indexed_child_cover` | Maps the original child-cover list through the inverse enumeration without increasing its length. |
| `indexed_child_bound_exists`, `childSupport_spec` | Derives a natural support bound beyond every child index. |
| `sumBelow_indicator_le_cover` | Bounds the number of distinct marked entries in a natural prefix by any list covering them. |
| `indexed_child_cap` | Derives the aggregate outgoing edge-count bound at the constructed child support from the original list-length bound. |
| `indexed_root_bound_exists`, `rootSupport_spec` | Derives a natural support bound beyond every actual root index from the original finite root cover. |
| `toNatPopulation` | Constructs an actual `PopulationCounting.InfiniteLabeledPopulation k d` with the derived edges, root marker, and support bounds. |
| `toNatPopulation_edge`, `toNatPopulation_root_iff` | Certifies exact preservation of original edges and actual roots by the constructed population. |
| `subcritical_impossible` | An input population and $`d < k`$ imply `False`. |
| `initial_vertices_are_roots` | Every enumerated original vertex at an index below $`k`$ has no original parent. |
| `at_least_k_distinct_roots` | Produces `roots : Fin k -> V` whose values are all original roots and whose values are pairwise distinct. |
| `alphabet_le_root_cover_length` | Every finite list covering all original roots has length at least $`k`$. |

The child-count proof filters the duplicate-free list `List.range n` by the indicator of an actual edge. This filtered list is still duplicate-free, and every member lies in the transported child cover. Its length is therefore bounded by the cover length. The equality between that filtered length and `sumBelow` is proved in `sumBelow_indicator_eq_filter_length`. Thus the counting assumption required by `InfiniteLabeledPopulation` is derived from the original local child cover; it is not a restatement supplied by the caller.

The root-support proof pulls the original finite root cover back through the inverse enumeration and invokes the checked finite-cover-to-natural-bound equivalence. The root marker is defined from actual parentlessness. The exact two-way root theorem rules out an additional root designation convention. Incoming labelled parents are transported using the enumeration's surjectivity, preserving the labels exactly.

The final consequences compose the existing [`PopulationCounting.infinite_subcritical_impossible`](../lean/SamuelAlexanderResearch/PopulationCounting.lean) and [`GeneralRootObstruction.initial_declared_root`](../lean/SamuelAlexanderResearch/GeneralRootObstruction.lean) with the constructed population. Injectivity of the enumeration then gives distinct roots in the original type. These are model-transfer results for the checked arguments; no new literature-priority claim is made.

## Scope and validation

The module is Std-only and its time type is abstract. It applies to a literal real-valued birth map only after the real order instances and finite-sublevel hypotheses are supplied by a separate checkable adapter; this file does not define or import `Real`. For hypotheses given as finite strict sublevels, the existing `BirthOrder.finiteSublevels_of_strict` supplies closed-sublevel finiteness when the time order has a point above every point. The optional Mathlib project owns the literal real specialization.

The construction is noncomputable and uses classical choice. It proves existence of the enumeration from the stated data, without assuming countability or asking for a supplied enumeration. It covers arbitrary finite label counts for degree impossibility and root counts. It does not add a positive arbitrary-finite-alphabet word-realization or classification theorem.

The module compiled without warnings using Lean 4.33.1:

```powershell
$env:ELAN_HOME = 'C:\Users\Owner\.elan'
& 'C:\Users\Owner\.elan\bin\lake.exe' build SamuelAlexanderResearch.PopulationReindex
```

All nine printed endpoints use only the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`. The proof-placeholder scan found no `sorry`, `admit`, custom axiom, opaque declaration, or `native_decide`. Existing proof modules and shared imports were not modified.
