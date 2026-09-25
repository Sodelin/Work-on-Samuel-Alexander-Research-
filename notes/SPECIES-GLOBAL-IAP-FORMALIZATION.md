# Global IAP, reflection, and whole-graph inspecies

The checked module is [`SpeciesGlobalIAP.lean`](../lean/SamuelAlexanderResearch/SpeciesGlobalIAP.lean). It imports only the existing Std-based `SpeciesBridge` module. Its generic theorems quantify over an arbitrary directed edge relation `E : Nat → Nat → Prop`; they do not assume acyclicity, chronological edges, finite roots, or finite children. The ambient vertex set is all natural numbers and is therefore infinite.

`Descendant E u v` retains the existing strict convention: a nonempty directed path from `u` to `v`. With a cycle, a vertex can be its own strict descendant. All generic proofs in this module handle that case. Finiteness is the existing finite-list-cover predicate `FiniteSupport`, already proved equivalent to boundedness for subsets of `Nat` in `SpeciesBridge`.

## Definitions and endpoints

`FiniteOrCofiniteDescendants E` says that, for every vertex `v`, its ambient descendant set is finite or its ambient non-descendant set is finite. `CofiniteDescendants E` requires the latter for every vertex.

| Checked endpoint in namespace `SpeciesGlobalIAP` | Exact content |
| --- | --- |
| `iap_whole_iff` | The whole graph has IAP iff `FiniteOrCofiniteDescendants E`. |
| `all_subsets_iap_iff` | Every subset has IAP iff `FiniteOrCofiniteDescendants E`. |
| `all_infinite_subsets_reflection_iff` | Every infinite subset satisfies REF iff `FiniteOrCofiniteDescendants E`. |
| `all_subsets_iap_iff_all_infinite_subsets_reflection` | The two quantified subset conditions above are equivalent. |
| `whole_specieslike_iff` | The whole graph is specieslike iff it is weakly connected and has `FiniteOrCofiniteDescendants E`. Whole-graph convexity is automatic. |
| `whole_inspecies_iff_cofinite_descendants` | The whole graph is an inspecies iff `CofiniteDescendants E`. |
| `whole_iap_iff_inspecies_of_infinite_descendants` | If every vertex has infinitely many ambient descendants, whole-graph IAP is equivalent to the whole graph being an inspecies. |
| `reflection_iff_empty_or_infinite` | If every vertex has infinitely many ambient descendants and has a finite-or-cofinite descendant set, a subset satisfies REF iff it is empty or infinite. |
| `psWhole_inspecies` | The actual unlabelled binary graph `PsEdge` has its whole vertex set as an inspecies. |
| `psReflection_iff_empty_or_infinite` | A subset of `PsEdge` satisfies REF iff it is empty or infinite. |

The new definitions of ancestral closure and inspecies are explicit:

- `AncestrallyClosed E S`: if `v` belongs to `S` and `u` is an ancestor of `v`, then `u` belongs to `S`.
- `InfinitaryGenus E S`: `S` is infinite and ancestrally closed.
- `Inspecies E S`: `S` is an infinitary genus and every infinitary genus contained in `S` contains all of `S`. This is inclusion-minimality among infinite ancestrally closed subsets, with no additional maximality, connectivity, or common-ancestor premise.

The species predicates IAP and REF come from [Alexander, arXiv:2602.05274v1](https://arxiv.org/html/2602.05274v1), Definitions 2 and 9. The infinitary-genus and inspecies definitions follow [Alexander, *Infinite graphs in systematic biology, with an application to the species problem*](https://arxiv.org/html/1201.2869), Definitions 3 and 4. Proposition 6 of that earlier work establishes the related cofinite-descendant property for members of an inspecies. These formalizations are direct deductions and whole-graph specializations of the definitions, with no claim of priority. The working prose specification is the independently reviewed `SPECIESLIKE-GENERALIZATION.md` in the companion research repository.

## Why the converses hold

For the REF converse, suppose a vertex has both infinitely many descendants and infinitely many non-descendants. The set consisting of that vertex together with its non-descendants is infinite. Its internal descendant set from that vertex is contained in a singleton, even when there are cycles. Consequently this set violates REF. The forward implication partitions any infinite subset into its internal descendant part and its part contained in the finite ambient non-descendant set.

For the inspecies converse, if a vertex `v` has infinitely many non-descendants, removing both `v` and all descendants of `v` leaves a proper infinite ancestrally closed subset. Excluding `v` explicitly makes this argument valid even for vertices with no descendants. Conversely, any infinite ancestral-closed subset must contain every vertex whose descendant set is cofinite: otherwise that entire subset would lie in a finite non-descendant set.

For `PsEdge`, the existing theorem `psNonDescendants_finite` supplies cofinite descendants at every vertex, and `psDescendants_infinite` supplies their infinitude. The new result that the whole set is an inspecies is compatible with the existing failure of the common-ancestor property: roots 0 and 1 prevent any one vertex from being an ancestor of every other vertex, although every vertex is an ancestor of all but finitely many vertices.

## Validation and scope

The module was compiled with Lean 4.33.1 using:

```powershell
$env:ELAN_HOME = 'C:\Users\Owner\.elan'
& 'C:\Users\Owner\.elan\bin\lake.exe' build SamuelAlexanderResearch.SpeciesGlobalIAP
```

All printed endpoints use only Lean's standard axioms `propext`, `Classical.choice`, and `Quot.sound`, or a subset of them. `all_subsets_iap_iff` and `whole_specieslike_iff` have no axiom dependencies. There are no proof placeholders, custom axioms, or `native_decide` calls.

These graph theorems are proved for all-natural-number vertex sets. The separate `BirthOrder` module constructs a natural-number enumeration from arbitrary infinite vertex types with locally finite ordered birth times; this file does not itself add a transport theorem for every species predicate. Literal real-number birthdate adapters belong to the optional Mathlib project. No eventually-periodic unavoidability result or further root-cone classification is asserted here.
