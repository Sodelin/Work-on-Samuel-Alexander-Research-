# Population counting: formal meaning and presentation bridge

The module [PopulationCounting.lean](../lean/SamuelAlexanderResearch/PopulationCounting.lean) closes the finite graph-count gap recorded in `DEGREE-BOUNDARY.md` and `FORMALIZATION-SCOPE.md`. It also proves subcritical impossibility for an infinite population on `Nat` already numbered in birth order. It imports only `Std` and was checked directly with Lean 4.33.1. This is an elementary counting formalization, with no novelty or literature-priority claim.

## Checked endpoints

All theorem names below are in namespace `PopulationCounting`. Let `N` be a prefix size, `R_N` its actual root count, `k` the number of required labels, and `d` the full child cap.

| Endpoint | Formally checked conclusion | Input and meaning |
|---|---|---|
| `double_count` | Sum of incoming degrees equals sum of outgoing degrees | Degrees count entries in one finite simple directed adjacency relation. |
| `nonroot_indegree` | Each nonroot has indegree at least `k` | An actual parent edge exists for every label below `k`; an ordered pair has only one label. |
| `edge_bounds`, `offspring_edge_bound` | `k * (N - R_N) <= edgeCount <= d * N`, hence `k * (N - R_N) <= d * N` | The inequalities are derived; they are not hypotheses. |
| `offspring_threshold` | `(k - d) * N <= k * R_N` | The finite population's local parent and actual child-count assumptions suffice. |
| `strict_offspring_size_bound` | `N <= (k * R_N) / (k - d)` when `d < k` | Natural division is the floor bound. |
| `gender_double_count`, `gender_edge_bound` | `N - R_N <= 2 * M_N` and `N - R_N <= 2 * F_N` | Edges are counted by a permanent Boolean attribute of their source vertex. |
| `binary_vertex_gender_abs_balance` | `Int.natAbs (M_N - F_N) <= R_N` | Each nonroot has a parent of each permanent gender; each vertex has at most two actual outgoing neighbors. |
| `ordered_prefix_closed` | The first `N` vertices are predecessor-closed | A strict increase in natural-number birth index along each edge implies closure. |
| `prefix_offspring_threshold`, `prefix_binary_gender_balance` | The same offspring and gender bounds for an explicitly closed prefix | The finite ambient graph is restricted, and local parent coverage and child caps are proved to survive restriction. |
| `critical_degree_conservation` | `D_N + E_N + C_N = k * R_N` | A finite ambient population with child cap `k`; the prefix is predecessor-closed; degrees are full ambient degrees. |
| `critical_degree_budget` | `D_N + E_N <= k * R_N` and `C_N <= k * R_N` | Nonnegativity follows from natural counts and the local degree assumptions used in conservation. |
| `no_unbounded_finite_prefixes` | No root-count-bounded family of finite populations has every size if `d < k` | This is a reusable finite-family corollary, distinct from the infinite graph theorem. |
| `infinite_subcritical_impossible`, `no_infinite_subcritical_population` | No `InfiniteLabeledPopulation k d` exists when `d < k` | The graph has vertex set `Nat`, edges go forward, each nonroot has every required label, roots are finitely supported, and every full child set has a finite support bound and actual count at most `d`. |

## Actual graph data and counts

`LabeledGraph N` stores `edge : Nat -> Nat -> Option Nat`. Its vertices are precisely the natural numbers less than `N`. At an ordered pair, `none` means no edge and `some l` means one edge with label `l`. This representation rules out parallel edges and assigning two labels to one edge. `no_self` excludes loops. Values outside the vertex range are ignored by the finite graph.

`edgeBit` is one exactly when the adjacency entry is present. `sumBelow N f` recursively sums `f 0` through `f (N - 1)`. `inDegree`, `outDegree`, `edgeCount`, root counts, gender counts, and crossing counts are all defined from those entries. The basic summation infrastructure, including interchange of the two finite sums, is proved by induction in this module. It requires no unavailable `Finset` or `Fintype` library.

`LabeledPopulation N k d` adds a root predicate, absence of incoming edges at roots, an incoming parent witness for every required label at each nonroot, and the pointwise bound `outDegree u <= d`. Label uniqueness is encoded by `Option Nat`, so the proof that `k` labels require at least `k` distinct edges is derived by counting the label fibers and interchanging their finite sums. The representation permits additional labels at or above `k`; this weakens the assumptions and does not weaken the conclusion. For `k > 0`, parent coverage and parentlessness identify the declared roots exactly. At `k = 0`, the theorems still hold, but the declared root predicate is not asserted to classify every parentless vertex.

`GenderedPopulation N` stores a single `gender : Nat -> Bool` function. Its two required parents have different source attributes, so one source cannot satisfy both requirements by using differently labelled edges. The final theorem uses the natural absolute value of the difference after coercing the counts to integers; an equivalent pair of one-sided inequalities is also exported.

The finite counting statements do not need acyclicity. They remain true for a broader class of finite graphs. Where a prefix is involved, predecessor closure is explicit. `ordered_prefix_closed` proves that a strict natural birth order is a sufficient condition; closure is not silently assumed from the word "prefix."

## Full degrees at the critical boundary

For a prefix of size `N` inside an ambient finite population of size `m`, `outgoingDeficit` is the sum of `k - outDegree` for vertices below `N`, where `outDegree` ranges over all `m` possible children. `incomingExcess` sums `inDegree - k` over nonroots below `N`, with incoming degrees also computed in the ambient graph. `crossingCount` counts every adjacency entry with source below `N` and target at least `N` but below `m`.

`incoming_prefix_degree` derives the absence of incoming contributions from outside the prefix. `outgoing_prefix_split` partitions full outgoing degrees into internal and outgoing crossing edges. These identities, together with the proved degree and root counts, give `D_N + E_N + C_N = k * R_N`. Thus a truncated prefix outdegree is never substituted for the full ambient outdegree in the deficit.

This critical-degree endpoint is currently for a **finite ambient graph**. The corresponding identity for full degrees in an infinite population, the lower bound `C_N >= k` after the final root, the sharper budget `D_N + E_N <= k * (R - 1)`, eventual degree regularity, and eventual constancy of crossing width are not claimed as checked by this module. The natural infinite representation below has the data needed for further work, but those additional endpoints have not been proved here.

## The infinite theorem is a graph theorem

`InfiniteLabeledPopulation k d` uses one adjacency relation on all of `Nat` and requires that every present edge `u -> v` satisfy `u < v`. For each source `u`, `childSupport u` is a natural number beyond all its actual children: `no_children_after` makes every later adjacency entry absent. `child_cap` bounds the sum of all present entries below that support. Together these express a cap on the **full outgoing neighbor set**. A separate `rootSupport` bounds all roots, and `fullRootCount` counts them exactly below that bound.

The theorem does not assume a family of prefixes or an aggregate edge inequality. `infinitePrefix` constructs the graph on the first `N` vertices. Forward edge order puts all required parents inside it. A proved finite-support lemma bounds its outgoing degrees by the full degrees and its root count by `fullRootCount`. These constructed prefixes contradict `no_unbounded_finite_prefixes` at `N = k * fullRootCount + 1` when `d < k`.

## Comparison with Alexander's definition

Alexander's [Definition 1](https://arxiv.org/html/1212.0186v2) uses an infinite directed graph, finitely many parentless roots, finitely many children at each vertex, real birthdates with finite sublevels and strict increase along edges, and one incoming edge of each required gender at every nonroot. His text also explains the fixed-vertex-gender specialization by assigning an edge its source's gender.

The finite module verifies the local edge counts and closed-prefix restriction directly. The infinite module assumes a chosen enumeration by `Nat`, with edges strictly increasing in that enumeration, and explicit finite support bounds for children and roots. A uniform child cap is an extra hypothesis of the degree-boundary result. The module itself uses that enumeration. BirthOrder and PopulationReindex now construct it from the arbitrary presentation, including finite sublevels and tied dates; RealBridges supplies the literal real-date degree/root statements. InfiniteConservation supplies the full infinite critical identity. See the current central coverage report for these composed endpoints.

The module does not address the existence of two-child fixed-vertex-gender populations avoiding a prescribed noneventually-periodic sequence, nor any periodicity or finite-state conclusion about population graphs.

## Reproduction and axiom audit

Run from the repository root on the original Windows host:

```powershell
$env:ELAN_HOME='C:\Users\Owner\.elan'
& 'C:\Users\Owner\.elan\bin\lake.exe' env lean lean/SamuelAlexanderResearch/PopulationCounting.lean
```

The pinned toolchain is `leanprover/lean4:v4.33.1`; the reported compiler is Lean 4.33.1, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. The direct module check exits 0 with no warnings. This lane did not edit root imports, the Lake configuration, or CI; integration into the aggregate build belongs to the coordinating lane.

The file contains `#print axioms` checks for its principal endpoints. All reported dependencies are subsets of Lean's standard `propext`, `Quot.sound`, and `Classical.choice`. The finite offspring and infinite subcritical endpoints, double counts, and critical conservation report only `propext` and `Quot.sound`. The final gender discrepancy and critical budget arithmetic additionally report `Classical.choice`. There is no `sorry`, user-declared `axiom`, or `native_decide` in the module, and no endpoint reports `sorryAx`.

A useful source audit command is:

```powershell
rg -n '\b(sorry|axiom|native_decide)\b' lean/SamuelAlexanderResearch/PopulationCounting.lean
```

It produces no matches (ripgrep exit 1). This source scan complements the kernel axiom output; it does not replace compilation.
