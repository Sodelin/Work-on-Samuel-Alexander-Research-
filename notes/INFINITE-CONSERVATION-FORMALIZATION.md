# Infinite critical-degree conservation and finite defects

[InfiniteConservation.lean](../lean/SamuelAlexanderResearch/InfiniteConservation.lean) closes the infinite critical-degree gaps left by `PopulationCounting.lean`. It proves the conservation identity using actual full degrees in one infinite graph, eventual exact degrees, and eventual constant crossing width. It also proves the stronger cut bound $`C_{N} \ge \frac{k(k+1)}{2}`$ after all roots, and the improved full defect budget $`D+E \le k\cdot R - \frac{k(k+1)}{2}`$. In the binary case these are $`C_{N} \ge 3`$ and $`D+E \le 2\cdot R - 3`$. The module uses the existing population model unchanged.

This is a Lean-checked elementary counting deduction. It makes no literature-priority claim. The population background is Alexander's [Definition 1](https://arxiv.org/html/1212.0186v2), with finite roots, finite child sets, and an increasing birth order. The formal model here is already enumerated by natural birth indices.

## Exact model and counted quantities

Let `p : InfiniteLabeledPopulation k k`. Its vertices are all natural numbers. `p.edge u v : Option Nat` represents at most one edge and one label at each ordered pair. Every present edge satisfies $`u < v`$; every declared root has no incoming edge; every other vertex has a parent edge with each label below $`k`$. For each source, `childSupport u` is a bound beyond all its children, and the number of actual outgoing edges below that support is at most $`k`$. `rootSupport` is a bound beyond all declared roots. No aggregate count, eventual regularity, or defect-support assumption has been added.

The prefix is the set of vertices less than $`N`$. The quantities are:

| Formal definition | Exact meaning |
|---|---|
| `PopulationCounting.fullOutDegree p u` | Number of all children of $`u`$, summed below its certified child-support bound. |
| `InfiniteConservation.fullInDegree p v` | Number of all parents of $`v`$, summed over sources less than $`v`$; birth order proves there are no others. |
| `prefixRootCount p N` | Actual declared root count below $`N`$, written $`R_{N}`$. |
| `PopulationCounting.fullRootCount p` | Actual full root count, written $`R`$. |
| `outgoingDeficit p N` | $`D_{N} = \sum_{u<N} (k - \operatorname{fullOutDegree} u)`$. |
| `incomingExcess p N` | $`E_{N} = \sum_{v<N, \operatorname{nonroot} v} (\operatorname{fullInDegree} v - k)`$. |
| `crossingCount p N` | $`C_{N}`$, the number of all edges from sources below $`N`$ to targets at or above $`N`$, including targets arbitrarily far beyond the prefix. |
| `localDefect p v` | The nonnegative outgoing deficit plus nonroot incoming excess at one vertex. |
| `totalDefect p N` | $`D_{N} + E_{N}`$, also proved equal to the sum of `localDefect` below $`N`$. |

The outgoing and incoming degrees in the deficit definitions are **full infinite-graph degrees**. Prefix-truncated outdegrees are not substituted for them. Natural subtraction does not hide a negative contribution: the existing full child cap and the proved `full_indegree_lower` justify both nonnegative defect terms. At roots the incoming excess is defined to be zero, and `full_indegree_root` proves their full indegree is zero.

For $`k > 0`$, coverage of a required label makes the declared roots exactly the parentless vertices. The formal theorems also allow the degenerate $`k=0`$ representation; in that case the declared root predicate need not classify every parentless vertex. The intended population interpretation uses positive $`k`$.

## Checked endpoints

All names below are in namespace `InfiniteConservation`.

| Endpoint | Formally checked statement |
|---|---|
| `conservation p N` | $`D_{N} + E_{N} + C_{N} = k \cdot R_{N}`$ for every prefix of the infinite graph. |
| `crossing_lower_after_roots p N hN` | $`k \le C_{N}`$ when $`\operatorname{rootSupport}\le N`$; this theorem even permits a general child cap $`d`$. |
| `crossing_upper p N` | $`C_{N} \le k \cdot R`$ for every prefix at the critical cap. |
| `sharp_defect_bound_after_roots p N hN` | $`D_{N} + E_{N} \le k \cdot (R - 1)`$ once all roots are inside. |
| `sharp_defect_bound p N` | The same sharp inequality for every prefix, by monotonicity of nonnegative defect sums. |
| `defects_stabilize p` | There is a finite prefix after which $`D_{N} + E_{N}`$ is constant. |
| `eventually_zero_local_defects p` | There is a finite index beyond which every vertex's local defect is zero. |
| `finite_total_defect p` | A finite support certificate for all local defects, with their full total at most $`k \cdot (R - 1)`$ and equality of that total in every larger prefix. |
| `eventually_regular p` | Every sufficiently late vertex is a nonroot with full indegree exactly $`k`$ and full outdegree exactly $`k`$. |
| `eventual_constant_crossing p` | There is a finite prefix after which the actual outgoing crossing count is constant. |
| `eventual_structure p` | One common tail has exact full degrees and constant crossing width, with $`k \le C \le k \cdot R`$. |
| `crossing_block_lower p N m hN` | The crossing count is at least $`\sum_{i<m} (k-i)`$ once all roots are inside. This holds for a general child cap $`d`$. |
| `crossing_triangular_lower p N hN` | $`\frac{k(k+1)}{2} \le C_{N}`$ once all roots are inside, independent of criticality. |
| `triangular_defect_bound p N` | $`D_{N} + E_{N} \le k\cdot R - \frac{k(k+1)}{2}`$ for every prefix at the critical cap. |
| `binary_crossing_lower p N hN` | At least three crossing edges after all roots in a binary population, for any finite child cap $`d`$. |
| `binary_defect_bound p N` | $`D_{N} + E_{N} \le 2\cdot R - 3`$ in a binary population with child cap two. |
| `finite_total_defect_triangular p` | A finite support certificate for all defects, with their full total bounded by $`k\cdot R - \frac{k(k+1)}{2}`$. |

`finite_total_defect` and its stronger triangular version certify the full infinite sum without introducing an infinite-sum library: they exhibit a finite prefix containing every nonzero summand, bound the sum there, and prove every larger prefix has exactly that sum. These are statements about the actual finite support of the defect function, not merely bounds on independently postulated prefix totals. The earlier $`k\cdot (R-1)`$ endpoints remain available, while the triangular endpoints state the stronger checked result.

## Proof route

For each prefix, $`\operatorname{ambientBound}(p,N)=N+1+\sum_{u<N}\operatorname{childSupport}(u)`$ contains the prefix and all its child supports. The existing `infinitePrefix` constructs a finite population on that ambient range. `finite_outdegree_eq`, `finite_indegree_eq`, and `finite_crossing_eq` prove equality of the relevant finite counts with the full infinite counts. Applying the previously checked finite conservation identity therefore gives the genuine infinite identity.

After all roots, vertex $`N`$ is a nonroot. Its $`k`$ distinct required incoming edges all come from vertices below $`N`$, so they are included in $`C_{N}`$. This gives the crossing lower bound. The conservation identity then supplies the sharp defect budget. Nonnegative monotonicity extends that budget to earlier prefixes.

The stronger count uses the first $`k`$ vertices after the cut. At vertex $`N+i`$, at most $`i`$ parents can lie inside the new block, because all parents precede their child and there is at most one edge per ordered pair. At least $`k-i`$ incoming edges therefore come from below $`N`$. These edges are disjoint across their different targets. Summing and double-counting the same adjacency entries gives $`C_{N} \ge \sum_{i<k}(k-i)`$. The module proves that this sum is exactly $`\frac{k(k+1)}{2}`$. Combining this with conservation gives the stronger full-defect budget. The hypotheses used here are explicit: $`N\ge\operatorname{rootSupport}`$, so all of these future vertices are nonroots. No critical child cap is needed until the defect-budget conclusion.

The residual budget `k*(R-1) - totalDefect p N` is a decreasing natural-valued sequence. The module reuses the existing `BinaryAvoidance.decreasing_nat_stabilizes` lemma. Once consecutive total-defect sums agree, their new local summand is zero. Outside the root support, the pointwise upper and lower degree bounds then give exact degrees $`k`$. Finally, conservation with stable root and defect counts gives stable crossing width.

## Boundaries

The results assume the existing natural birth-order enumeration and explicit finite support bounds in `InfiniteLabeledPopulation`. This module does not construct an enumeration from an arbitrary real-valued birthdate model; that conversion is a separate bridge. It does not prove graph periodicity, a finite-state presentation, a rigidity theorem when the minimum crossing width is attained, or a computable bound for the index of the last defect. The tail index is existential, as required by the finite-defect conclusion.

The new endpoints prove exact full indegrees and outdegrees. A separate theorem spelling out uniqueness of the parent with each label is not exported here. No assertion is made about the unresolved two-child fixed-vertex-gender avoidance problem.

## Reproduction and axiom audit

From the repository root on the original Windows host:

```powershell
$env:ELAN_HOME='C:\Users\Owner\.elan'
& 'C:\Users\Owner\.elan\bin\lake.exe' env lean lean/SamuelAlexanderResearch/InfiniteConservation.lean
& 'C:\Users\Owner\.elan\bin\lake.exe' build SamuelAlexanderResearch.InfiniteConservation
```

The pinned toolchain is Lean 4.33.1. The direct check and targeted build both succeed with exit code 0 and no warnings. The module imports `PopulationCounting` and reuses one general natural-number stabilization theorem from `BinaryAvoidance`; it adds no package dependency.

The file prints axioms for its principal endpoints. Conservation, crossing bounds, and sharp defect bounds report only `propext` and `Quot.sound`. Stabilization, finite support, and eventual-structure endpoints additionally report `Classical.choice`. There are no user-declared axioms, no `sorry`, no `native_decide`, and no endpoint reports `sorryAx`.

Only the new module and this note belong to this implementation lane. Root imports, shared status notes, and CI integration are handled by the coordinating lane.
