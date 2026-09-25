# Finite-boundary parent-label repair

[`BoundaryRepair.lean`](../lean/SamuelAlexanderResearch/BoundaryRepair.lean) resolves the deletion-only repair problem on a fixed retained vertex set for the existing binary population model. It proves an exact existence criterion, a canonical optimal repair, preservation of eligibility and avoidance, and the exact repairs for both common-ancestor cones of the source graph.

The original graph `E` is a `BinaryPopulation.BinaryNatPopulation`. The retained subset `S` is fixed. A vertex in `S` is deficient when at least one Boolean label has no incoming original edge from a parent in `S`:

```text
Deficient E S v := S v and exists b, no u in S has E u v b.
```

Original retained roots are included in this predicate: they are already parentless and need no incoming edges removed. The newly created roots are exactly the deficient vertices that were not original roots.

The canonical `Repair E S` keeps the original labelled edge `u -> v` precisely when both endpoints belong to `S` and `v` is not deficient. Thus it deletes all remaining incoming edges at deficient vertices, and no other retained original edge. A lost parent is only evidence of possible deficiency; losing one parent does not justify cutting a vertex whose other retained parents still supply every label.

## Exact existence and optimality statements

For every fixed infinite `S`, `finite_deficiency_iff_repair_exists` proves:

```text
The deficient set is finite
  iff
there is an eligible deletion-only repair on exactly S.
```

The proof uses the actual root predicate. Every admissible repair must make each deficient vertex parentless, because deleting further edges cannot supply a missing label. Finitely many roots are therefore possible only if the deficient set is finite. Conversely, the canonical repair makes exactly that set its retained roots, preserves chronology and finite children, and leaves all incoming labels at every nonroot.

`AdmissibleRepair E S F` quantifies over labelled subrelations of the original induced graph on the same retained vertices, with the usual incoming-label rule at every retained nonroot. `repair_greatest` proves that every such `F` is a subrelation of `Repair E S`. Consequently the canonical deleted edge set is inclusion-minimal, and `repair_minimal_roots` proves that its root set is inclusion-minimal as well. This is stronger than merely producing one sufficient repair. It does not optimize over a changed retained vertex set, added edges, or relabelled edges.

Chronology also proves `repair_deleted_edges_bounded`: if the deficient set is finite, one natural bound contains both endpoints of every deleted retained edge. Thus the repair changes only finitely many edges, not just finitely many target vertices.

## Cofinite subsets and actual population transport

If only finitely many original vertices are deleted, finite branching makes the set of their retained children finite. Every deficient retained vertex is either an original root or one of those children. Thus `deficient_finite_of_cofinite` derives the finite-deficiency hypothesis. Cofiniteness also ensures the retained set remains infinite.

`cofinite_repair_population` proves the full retained population conditions. The more general `repair_population_of_finite_deficiency` allows an infinite complement, requiring only infinitude of `S` and finiteness of its actual deficiency set. The `ProductiveCore` subtype adapter then constructs a birth-ordered enumeration and proves an actual `BinaryNatPopulation`; deleted ambient indices never become vertices or phantom roots.

`finite_boundary_repair_theorem` packages that reindexed eligibility, preservation of any supplied original uniform child cap, preservation of every avoided target, and exact correspondence between reindexed roots and original deficient retained vertices. Every repaired infinite path is an original infinite path. The reverse path implication is not claimed: deletion can remove realizations.

Principal endpoints in namespace `BoundaryRepair`:

| Endpoint | Checked result |
| --- | --- |
| `deficient_finite_of_cofinite` | Finite deletion, finite original roots, and finite children imply finite deficiency. |
| `repair_root_iff` | Retained repaired roots are exactly deficient vertices. |
| `cofinite_repair_population` | The canonical repair of a cofinite subset is eligible on that subset. |
| `finite_deficiency_iff_repair_exists` | Exact existence criterion for an eligible deletion-only repair on a fixed infinite subset. |
| `repair_greatest`, `repair_minimal_roots` | The canonical repair keeps the greatest permissible edge relation and has the smallest permissible root set. |
| `repair_deleted_edges_bounded` | Only finitely many retained edges are deleted. |
| `finite_boundary_repair_theorem` | Actual reindexed population, preserved cap and avoidance, and exact root correspondence. |
| `ps_c0_repair_roots`, `ps_c1_repair_roots` | Exact repaired roots in the two source cones. |
| `ps_c0_cut_edges`, `ps_c1_cut_edges` | Exact retained original edges that must be cut in those cones. |
| `ps_c0_repair_not_connected` | The canonical repair of `C0` disconnects the retained graph. |
| `ps_c1_repair_shifted_geometry` | The repair of `C1`, shifted down by one, has exactly `PsEdge` geometry. |

## Exact two-cone calculation

These results concern every actual target-dependent labelled graph `BinaryAvoidance.Edge s`, with the unchanged `SpeciesCones.C0` and `C1` definitions.

| Retained set | Deficient/repaired-root set | Deleted retained original edges | Geometric consequence |
| --- | --- | --- | --- |
| `C0 = {0} union {v | 2 <= v}` | `{0,2,3}` | `0 -> 2` and `2 -> 3`, with their original labels | Zero is isolated; whole retained connectedness fails. |
| `C1 = {v | 1 <= v}` | `{1,2}` | `1 -> 2`, with its original label | On vertices `u+1,v+1`, the repaired unlabelled adjacency is exactly `PsEdge u v`. |

The cut-edge theorems identify edges removed from the original induced graph; edges incident to an already deleted vertex are not counted as additional repair cuts. The general optimality theorem applies to these cases, so every admissible repair on the same retained vertices must remove the displayed edges and retain at least the displayed roots. The connectedness failure shows why eligibility and avoidance preservation must not be silently upgraded to preservation of all specieslike or common-ancestor properties.

## Scope and verification

The formal model uses functional Boolean-labelled edges and natural birth indices. No new arbitrary-finite-alphabet or real-date adapter is added. The criterion and optimality statements quantify over fixed retained vertices and edge deletion only; optimization that also deletes additional retained vertices is a different problem. The finite/cofinite boundary analysis is independent of whether the starting subset was presented as a specieslike cluster or a common-ancestor cone.

This is a direct structural deduction from the population axioms. No literature-priority claim is made. Alexander's definitions and the manuscript's actual source construction retain their attribution.

Checked with Lean 4.33.1:

```powershell
$env:ELAN_HOME = 'C:\Users\Owner\.elan'
& 'C:\Users\Owner\.elan\bin\lake.exe' build SamuelAlexanderResearch.ProductiveCore SamuelAlexanderResearch.BoundaryRepair
```

Selected printed endpoints use only `propext`, `Classical.choice`, and `Quot.sound`. There are no proof placeholders, custom axioms, or `native_decide` calls. Existing modules, shared imports, audits, and configurations were not modified.
