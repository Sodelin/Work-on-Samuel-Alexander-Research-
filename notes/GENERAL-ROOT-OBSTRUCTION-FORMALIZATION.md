# General finite-alphabet root obstruction

[`GeneralRootObstruction.lean`](../lean/SamuelAlexanderResearch/GeneralRootObstruction.lean) proves that the first `k` vertices are roots in a simple edge-labelled graph whose natural-number indices strictly increase along every edge and whose nonroots receive all `k` required labels. Consequently there are at least `k` distinct roots. If `k ≥ 2`, the whole graph cannot satisfy the common-ancestor property.

This extends the earlier binary root obstruction to arbitrary natural alphabet size. It uses local graph conditions; finite roots, finite children, and a uniform child cap are not hypotheses of the generic result.

## Generic model

`GeneralRootObstruction.ChronologicalLabelledGraph k` has exactly three fields:

1. `edge : Nat → Nat → Option Nat`, so an ordered vertex pair carries at most one edge label.
2. `birth_order`, requiring `u < v` whenever `edge u v` is present.
3. `parent_of_label`, requiring an incoming edge carrying every label `label < k` whenever the destination has at least one incoming edge.

Roots are defined from the actual graph as vertices having no incoming edges. The generic model has no independently supplied root marker. It allows labels outside the required range; those extra labels do not weaken the conclusion. The result is valid for `k = 0` as well, where the guaranteed initial root segment is empty. The common-ancestor obstruction specifically assumes `2 ≤ k`.

## Proof and endpoints

All names below are in namespace `GeneralRootObstruction`.

| Endpoint | Checked statement |
| --- | --- |
| `no_parent_at_or_after` | Every parent of `v` has index strictly below `v`. |
| `incomingCount_le_vertex` | The full incoming count of vertex `v` is at most `v`. |
| `incomingCount_lower` | If `v` has any parent, its full incoming count is at least `k`. |
| `initial_vertex_root` | Every `v < k` is a root of the actual edge relation. |
| `at_least_k_distinct_roots` | There exists a duplicate-free list of length `k` consisting of roots; the witness is `List.range k`. |
| `not_commonAncestor` | For `2 ≤ k`, the whole graph has no common ancestor. |

The lower incoming-count bound follows by counting label indicators. Each required label contributes at least one incoming edge. Since one ordered pair carries only one optional label, different labels cannot be accounted for by the same parent. The upper bound follows because every actual parent belongs to `{0, …, v - 1}`. At `v < k` the two bounds contradict the existence of a parent.

The common-ancestor proof uses roots 0 and 1. No nonempty directed path can end at a root. An alleged ancestor of every other whole-graph vertex therefore cannot cover both roots. The ancestry and common-ancestor predicates are reused from `SpeciesBridge` without changing their strict-path convention.

## Existing infinite-population model

`ofInfinitePopulation` constructs the generic local model from `PopulationCounting.InfiniteLabeledPopulation k d`. Its edge function is the original function unchanged, recorded by the reflexive theorem `ofInfinitePopulation_edge`. A vertex with an incoming edge cannot be marked as a root, by `root_no_parents`; the existing `parent_of_label` field then supplies its required labelled parents.

The following additional endpoints are checked:

- `fullInDegree_le_vertex` gives `InfiniteConservation.fullInDegree p v ≤ v`.
- `initial_declared_root` proves `p.root v = true` for every `v < k`, using the existing `full_indegree_lower` theorem together with the new upper bound.
- `initial_population_roots` combines the declared-root statement with actual graph roothood.
- `alphabet_le_fullRootCount` proves `k ≤ PopulationCounting.fullRootCount p`. It counts the initial `k` declared roots and applies the existing finite-support root-count bound.
- `population_not_commonAncestor` proves whole-graph CA failure when `2 ≤ k`.
- `population_root_obstruction` combines the full root-count lower bound and CA failure.

The child cap and child support fields of `InfiniteLabeledPopulation` are inherited by these corollaries but are unused in the local root obstruction. Its finite-root support is needed only to interpret and bound `fullRootCount`. No aggregate incoming-count or root-count inequality is assumed.

## Scope and validation

The statements concern functional edge labels, rather than a multigraph that permits parallel differently labelled edges from the same parent. They use natural birth indices. The separate `BirthOrder` module and optional real-date adapters handle enumeration and real birthdates; this file adds no real-number adapter.

This is a direct counting consequence of the local population axioms and [Alexander's common-ancestor definition](https://arxiv.org/html/2602.05274v1), with no literature-priority claim. Generalizing the root obstruction to `k` labels does not prove an arbitrary-finite-alphabet word classification. In particular, this file does not extend the project's binary positive unavoidability endpoint to larger alphabets.

The module compiled with Lean 4.33.1 and the existing Std-only project:

```powershell
$env:ELAN_HOME = 'C:\Users\Owner\.elan'
& 'C:\Users\Owner\.elan\bin\lake.exe' build SamuelAlexanderResearch.GeneralRootObstruction
```

Printed endpoints use only Lean's standard axioms `propext`, `Classical.choice`, and `Quot.sound`, or a subset of them. The root-count and CA corollaries use only `propext` and `Quot.sound`. There are no proof placeholders, custom axioms, or `native_decide` calls. Earlier modules, including the existing binary `RootObstruction`, are unchanged.
