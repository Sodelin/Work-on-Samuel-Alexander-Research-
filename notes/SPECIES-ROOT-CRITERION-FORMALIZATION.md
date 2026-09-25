# The general root-cone criterion

[`SpeciesRootCriterion.lean`](../lean/SamuelAlexanderResearch/SpeciesRootCriterion.lean) proves the root-cone criterion from the merged [`SPECIESLIKE-GENERALIZATION.md`](SPECIESLIKE-GENERALIZATION.md). The graph is an arbitrary relation `E : Nat → Nat → Prop`. All four species predicates are reused from `SpeciesBridge`, with strict nonempty-path descendants and ambient-graph convexity and reflection.

The central conclusion is exact: assuming every vertex lies in a root cone, **every root cone has IAP if and only if the inclusion-maximal IAP + convexity + common-ancestor + reflection subsets are exactly all root cones**. Root coverage is also derived from the hypothesis that each edge $u \to v$ has $u < v$.

## Exact definitions and semantic bridges

`Cone E r` contains $r$ and every strict descendant of $r$. `RootCovered E` says that every vertex belongs to such a cone whose initial vertex has no incoming edges. `RootConesIAP E` requires IAP for every root cone.

`FourAxioms E S` is the conjunction `IAP E S ∧ Convex E S ∧ CommonAncestor E S ∧ Reflection E S`. `MaximalFourAxioms E S` adds inclusion-maximality among subsets satisfying exactly this conjunction. `RootConeClassification E` says that a subset is maximal in this class if and only if it equals `Cone E r` for a root $r$.

The new definitions are parameterized by $E$, whereas the existing `SpeciesCones` module specializes to `PsEdge`. The checked bridges `cone_ps_eq`, `fourAxioms_ps_iff`, and `maximalFourAxioms_ps_iff` are all definitional equalities or equivalences proved by reflexivity. The existing exact two-cone theorem and its definitions remain unchanged.

## Checked statements

All names below are in namespace `SpeciesRootCriterion`.

| Endpoint | Hypotheses and conclusion |
| --- | --- |
| `rootCovered_of_strict_birth_order` | From $\forall  u v, E u v \to u < v$, proves `RootCovered E`. |
| `cone_weaklyConnected` | Every vertex cone is weakly connected in its induced subgraph. No root premise is needed. |
| `cone_convex`, `cone_commonAncestor`, `cone_reflection` | Every vertex cone satisfies these three predicates. |
| `cone_specieslike` | A vertex cone with IAP is specieslike. |
| `root_cone_subset_iff_root_eq` | The cone of a root $r$ is contained in another vertex's cone iff that vertex equals $r$. In particular, distinct root cones are incomparable by inclusion. |
| `root_cone_maximal` | A root cone with IAP is a maximal four-property set. This direction needs no coverage assumption. |
| `maximalFourAxioms_iff_root_cone` | Under root coverage and IAP for all root cones, the exact maximal family is all root cones. |
| `root_cone_criterion` | Under root coverage, `RootConesIAP E ↔ RootConeClassification E`. |
| `root_cone_criterion_of_strict_birth_order` | The same equivalence with strict natural edge order as its sole background hypothesis. |
| `maximalFourAxioms_specieslike` | Under coverage and root-cone IAP, every maximal four-property set is also specieslike. |
| `every_vertex_in_maximal_four_cluster` | Under those hypotheses, every vertex lies in a maximal four-property set that is also specieslike. |

The root-coverage proof uses strong induction on the natural vertex index. A vertex with no parents is a root. Otherwise a parent has a smaller index and already belongs to a root cone; adjoining the final edge places the child in that cone.

A cone is closed under all descendants of its members. This proves convexity and reflection directly, including cases where the cone is finite. Paths from its initial vertex prove induced weak connectivity, and that vertex witnesses the common-ancestor property. For maximality, a common-ancestor set containing a root has to use that root as its common ancestor, since a root has no strict ancestor. It therefore cannot leave the root's cone. Conversely, root coverage places any common-ancestor set inside some root cone, and IAP for that cone supplies a qualifying superset.

## Assumptions and limits

Finite roots, finite children, an outdegree cap, edge labels, and globally infinite descendants are not required by this criterion. In particular, a finite cone or an isolated root is not excluded. Distinct cones may overlap; incomparability by inclusion does not imply disjointness. Their maximality is within the four-property class, while their specieslike status is proved separately. They need not be maximal among all specieslike sets without the common-ancestor and reflection requirements.

These results are direct deductions from [Alexander's 2026 definitions](https://arxiv.org/html/2602.05274v1), related to the root-clade observation preceding Example 15 and the multiple-root example in Example 14. No literature-priority claim is made. The earlier graph-specific `PsEdge` classification remains a separate checked specialization. No theorem about labelled word realization inside a cone is claimed: removing vertices can remove required incoming labelled parents.

## Validation

The module compiled with Lean 4.33.1 and the existing Std-only project:

```powershell
$env:ELAN_HOME = 'C:\Users\Owner\.elan'
& 'C:\Users\Owner\.elan\bin\lake.exe' build SamuelAlexanderResearch.SpeciesRootCriterion
```

All printed endpoints use only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`, or a subset of them. The semantic bridges, `cone_weaklyConnected`, `root_cone_maximal`, and `every_vertex_in_maximal_four_cluster` have no axiom dependencies. There are no proof placeholders, custom axioms, or `native_decide` calls.
