# Productive pruning and cluster behavior

[`ProductiveCore.lean`](../lean/SamuelAlexanderResearch/ProductiveCore.lean) proves the whole-population pruning statement in proposal 8 and separates two different notions of maximal cluster. The input population is the existing `BinaryPopulation.BinaryNatPopulation`; the species and inspecies predicates are the existing `SpeciesBridge` and `SpeciesGlobalIAP` definitions. No enumeration, infinite path, or pruning conclusion is an input.

For an unlabelled natural-index graph `E`, the productive set is

```text
Core E v := infinitely many w are strict descendants of v in E.
```

The strict descendant relation is the existing nonempty directed-path relation. The retained graph is the actual induced graph on this set. Deleted natural indices are not treated as population vertices: the module constructs a birth-ordered enumeration of the retained subtype, using `BirthOrder`, and proves an actual `BinaryNatPopulation` for the pulled-back labels.

## Whole-population theorem

Finite roots, finite children, and strictly increasing natural birth indices imply that the productive set is infinite. The proof first derives a productive root cone from root coverage and a finite-union argument. A productive vertex has a productive child, since otherwise its finitely many children would each have finite descendant cones. Repeating this existence argument gives productive vertices beyond every natural bound. No incoming-label assumption or whole-graph IAP is needed for this graph-theoretic infinitude result.

Every ancestor of a productive vertex is productive. Consequently pruning preserves all original parents of every retained vertex. Original roots that remain retained are precisely the induced roots; all required incoming Boolean labels survive, and child sets only shrink. Uniform child caps are preserved whenever one is supplied, but a uniform cap is not required merely to construct the eligible core.

Whole-graph IAP is used for the stronger species conclusion. A productive vertex cannot have finitely many descendants, so IAP makes its ambient non-descendants finite. This proves both that the retained set is an inspecies in the ambient graph and that the entire reindexed population is an inspecies. Its whole graph is also specieslike, with connectedness proved from common sufficiently late descendants.

The stronger path statement is exact: productive pruning preserves the full infinite word language. Every vertex on an infinite chronological path has infinitely many later path vertices as descendants. Conversely, every retained path is an original path. Finite paths need not be preserved, since they may end in material that is pruned.

Principal endpoints in namespace `ProductiveCore`:

| Endpoint | Checked result |
| --- | --- |
| `core_infinite` | Finite roots, finite children, and strict natural edge order imply an infinite productive set. |
| `core_ancestrallyClosed`, `closed_root_iff` | All ancestors are retained, and retained induced roots are exactly retained original roots. |
| `core_population` | The retained core satisfies the full labelled population conditions on its actual vertex subset. |
| `reindexed_population` | Any input `PopulationOn` becomes the existing `BinaryNatPopulation` by a constructed subtype enumeration. |
| `reindexed_core_whole_inspecies` | The whole reindexed core is an inspecies when the original whole graph has IAP. |
| `reindexed_core_whole_specieslike` | The whole reindexed core is connected, IAP, and convex. |
| `reindexed_core_language_iff` | An infinite Boolean word is realized after pruning if and only if it was realized before pruning. |
| `productive_core_theorem` | Packages eligibility, induced-core inspecies, the same child cap, and preservation of every avoided target. |

`PopulationOn` is a retained-subset interface, not a replacement conclusion hidden in the hypotheses. It requires uniqueness of edge labels, infinitude of the retained set, strict chronology, finite retained children, finitely many retained actual roots, and incoming-label coverage at retained nonroots. `core_population` derives those fields from the original population. `reindexed_population` proves the bridge to the preexisting model; natural date prefixes follow from the retained natural birth indices.

## Maximality must be distinguished

The unrestricted predicate `SpeciesBridge.MaximalSpecieslike` means inclusion-maximality among weakly connected, IAP, convex sets in the fixed ambient graph. It does **not** include common ancestry or reflection as constraints on competing supersets.

For that exact predicate, `maximal_specieslike_descendantClosed` proves descendant closure under strict natural birth order. If a descendant `w` were missing, adjoin the ancestors of `w` that themselves descend from an old member. The added part is finite, since its vertices have indices at most `w`. The extension is convex and connected. Convexity of the old cluster forces every genuinely new vertex to have no descendant in the old cluster, so IAP survives as well. Maximality forces `w` into the original set. The finite-past step is explicit; this file does not claim an arbitrary well-founded-order version.

It follows that unrestricted maximal clusters satisfy reflection and that local productive pruning agrees with intersection with the ambient productive set:

```text
RelativeCore E S = {v | S v and Core E v}.
```

Here `RelativeCore E S` means retained vertices having infinitely many descendants in the graph induced on `S`. The endpoints are `maximal_specieslike_reflection` and `maximal_cluster_pruning_commutes`.

The CA/REF-constrained notion is different. `SpeciesRootCriterion.MaximalFourAxioms` is maximality among IAP, convex, common-ancestor, reflection sets. **Descendant closure is false for this notion.** The module checks the shared-root two-ray example corresponding to Alexander's 2026 Example 14(2): zero has children one and two, and each ray advances by two. Zero together with the odd ray is specieslike and maximal for all four constrained axioms, yet omits the descendant two. Its graph satisfies `NaturalDateBiosphere`. The endpoint `constrained_maximum_not_descendantClosed` records the complete contrast. This is an unlabelled biosphere example; it is not asserted to satisfy the stronger binary incoming-label population axioms.

Productive pruning still commutes for constrained clusters by a different proof. `relativeCore_eq_inter_of_convex_reflection` requires only convexity and reflection, and `four_axioms_pruning_commutes` applies it to the existing four-axiom package. Reflection gives infinitely many internal descendants, and convexity keeps the paths to them inside the subset. No descendant-closure claim is used.

Arbitrary nonmaximal specieslike subsets can behave differently. `nonmaximal_cluster_productivity_counterexample` uses the actual source geometry `PsEdge` and the cluster `{0}`: zero is productive in the ambient graph, but the induced singleton has no productive vertex. Thus the unrestricted-maximal and reflection assumptions cannot simply be omitted.

## Scope, attribution, and verification

The labelled eligibility and language endpoints use Boolean labels and natural birth indices. The unlabelled pruning and cluster lemmas are independent of label cardinality. Earlier birth-order adapters make chronological presentations available, but no new literal-real adapter is added in this module. No empirical species interpretation follows from these graph axioms.

Productive pruning, finite-union arguments, and the general role of infinite paths are classical. Alexander's inspecies definitions and cofinite-descendant results are the prior framework. The shared-root two-ray pattern is an existing source example, not a new counterexample-priority claim. The contribution recorded here is the precise checked simultaneous pruning statement and the distinction between the two maximality quantifiers.

Checked with Lean 4.33.1 and Std-only imports:

```powershell
$env:ELAN_HOME = 'C:\Users\Owner\.elan'
& 'C:\Users\Owner\.elan\bin\lake.exe' build SamuelAlexanderResearch.ProductiveCore
```

The selected printed endpoints use only `propext`, `Classical.choice`, and `Quot.sound`. There are no proof placeholders, custom axioms, or `native_decide` calls. Existing proof modules, aggregate imports, and shared audit files were not modified.
