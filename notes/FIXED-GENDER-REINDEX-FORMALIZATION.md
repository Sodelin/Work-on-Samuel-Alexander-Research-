# Retained-subset fixed-gender reindexing

[`FixedGenderReindex.lean`](../lean/SamuelAlexanderResearch/FixedGenderReindex.lean) closes the retained-subset model interface. From an actual `FixedGenderLift.FixedGenderPopulation E S g cap`, it constructs a birth-ordered bijection between natural numbers and the retained subtype `{x : Nat // S x}`, proves that source-gender labels give a `BinaryNatPopulation`, and transports the checked positive realization theorem back into $`S`$.

The final theorem `fixedGender_cap_three_classification` is unconditional: a binary word is realized in every retained-subset fixed-gender population with child cap at most 3 if and only if it is eventually periodic. The proof imports the checked positive theorem and the checked productive-core avoiding witness. Neither an enumeration nor a positive theorem is supplied as an endpoint premise.

## Exact models

The input is the existing `FixedGenderPopulation E S g cap` definition, unchanged. It requires an infinite retained subset $`S`$, strict natural birth order along edges between retained vertices, finite retained birthdate prefixes, finitely many retained roots of `Induced E S`, a finite-list child cover of length at most `cap` at each retained vertex, and a retained incoming parent of each Boolean gender at every retained nonroot.

The reindexed vertex at index $`i`$ is the natural value of the constructed subtype element `enumeration population |>.toFun i`. Its labelled edges are exactly

```text
LabelledEdge population i j label
  iff E (vertex population i) (vertex population j)
      and g (vertex population i) = label.
```

Thus the label is the fixed gender of the source. Every reindexed vertex is retained, and every retained vertex occurs exactly once. A deleted ambient index is never a vertex in this model.

`RealizesOn E S g target` means that there is an infinite natural-index path such that, for every time $`k`$, the current vertex belongs to $`S`$, the next edge belongs to $`E`$, and the source gender equals `target k`. Membership of every next vertex follows from the same assertion at time $`k+1`$. The theorem `realizes_reindex_iff` proves exact equivalence with `BinaryPopulation.Realizes` in the reindexed graph.

## Checked construction and endpoints

All names below are in namespace `FixedGenderReindex`.

| Endpoint | Checked content |
| --- | --- |
| `retained_list_cover` | Converts an ambient finite list cover to a retained-subtype cover without increasing its length. |
| `retained_infinite` | Derives infinitude of the retained subtype from `InfiniteSupport S`. |
| `retained_finiteSublevels` | Derives finite closed birthdate sublevels on the subtype from the supplied finite strict prefixes. |
| `enumeration` | Constructs the birth-ordered enumeration using `BirthOrder.orderedEnumeration`. |
| `vertex_retained`, `vertex_injective`, `vertex_surjective`, `vertex_nondecreasing` | Certify the image, bijection, and birth order. |
| `forgetLabels_iff` | The unlabelled adjacency is exactly $`E`$ on the enumerated retained vertices. |
| `root_iff` | A reindexed vertex is a root iff its retained original vertex is a root of `Induced E S`. |
| `finiteSupport_reindex` | Transports a finite retained ambient predicate to a finite predicate on enumeration indices. |
| `reindexed_child_cap` | Preserves the same numerical child cap after reindexing. |
| `reindexed_strict` | Every reindexed edge increases the natural index strictly. |
| `reindexed_binary_population` | Proves every axiom of the actual `BinaryNatPopulation` for `LabelledEdge population`. |
| `realizes_reindex_iff` | Transports realization in both directions between the reindexed graph and the retained graph. |
| `eventuallyPeriodic_realized` | Every eventually periodic binary target is realized inside every input retained fixed-gender population, at any cap for which that population exists. |
| `fixedGender_cap_three_classification` | `FixedGenderUnavoidable 3 s ↔ EventuallyPeriodic s`. |

The child-cover proof filters the original list into the subtype and then maps its members to their enumeration indices. Filtering cannot increase length, and mapping preserves length, so the original cap is retained. Root finiteness uses the same subtype-cover transport, together with the exact root equivalence. In particular, the fact that a deleted ambient index is vacuously a root of an induced relation does not add it to the reindexed root set.

The positive endpoint invokes [`PositiveUnavoidability.eventuallyPeriodic_realized`](../lean/SamuelAlexanderResearch/PositiveUnavoidability.lean) on the proved reindexed population, then maps its infinite path through the constructed enumeration. The negative direction of the cap-3 classification invokes [`FixedGenderLift.core_fixedGenderPopulation` and `core_avoids`](../lean/SamuelAlexanderResearch/FixedGenderLift.lean): the productive core supplies an actual cap-3 counterexample for every target that is not eventually periodic. This is a composition of the existing mathematical inputs, with no literature-priority claim.

## Scope and validation

This adapter is for retained subsets of natural-number vertices with the natural birth order specified by `FixedGenderPopulation`. It uses Boolean fixed source genders. A cap of 3 means a bound of at most 3 children; it does not require every vertex to have exactly 3 children. No real-birthdate adapter or arbitrary-finite-alphabet positive theorem is asserted in this module. The negative witness already has additional specieslike and inspecies properties in `FixedGenderLift`; the displayed new classification quantifies over the full retained fixed-gender cap-3 class.

The Std-only module compiled with Lean 4.33.1:

```powershell
$env:ELAN_HOME = 'C:\Users\Owner\.elan'
& 'C:\Users\Owner\.elan\bin\lake.exe' build SamuelAlexanderResearch.FixedGenderReindex
```

All printed endpoints use only the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`. There are no proof placeholders, custom axioms, or `native_decide` calls. The input models and imported proof modules were not modified.
