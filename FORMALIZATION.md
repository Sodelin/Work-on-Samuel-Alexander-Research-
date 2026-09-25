# Checked mathematics and exact remaining scope

The default Lean library contains eleven modules. Lean 4.33.1 builds them together, and all 80 selected endpoints pass the axiom audit. The developments use the bundled standard library, with rational arithmetic lemmas from `Init`; there is no Mathlib dependency. The [final audit receipt](verification/formal-audit.json) records the exact source hashes.

This is a collection of explicit graph proofs, a formalized avoidance construction, and algebraic and reachability reductions. It is not a complete formalization of either source paper. In particular, the one displayed classification equivalence still has its positive unavoidability theorem as a premise.

## Results

| Development | What Lean proves | Important boundary |
|---|---|---|
| [Population counting](lean/SamuelAlexanderResearch/PopulationCounting.lean) | Actual finite incoming/outgoing edge counts agree; one parent per label implies the count bound; `k*(N-R) <= d*N`, `(k-d)*N <= k*R`, and the subcritical floor bound follow. Closed-prefix restriction preserves the hypotheses. | The old arithmetic-only [DegreeBounds](lean/SamuelAlexanderResearch/DegreeBounds.lean) module is retained, but is no longer the only counting evidence. |
| Infinite offspring threshold, in the same module | No single infinite naturally ordered population can have finitely many roots, the required `k` incoming labels at each nonroot, and child cap `d<k`. Finite prefixes and their count bounds are constructed from that graph. | Construction of a natural birth-order enumeration from arbitrary real birthdates with finite sublevels is not encoded. |
| Fixed vertex genders, in the same module | With one parent of each permanent Boolean gender and child cap two, `Int.natAbs(M-F) <= R` follows from actual adjacency counts, including for predecessor-closed prefixes. | This does not settle the two-child fixed-gender avoidance question. |
| Critical-degree conservation, in the same module | For a predecessor-closed prefix in a finite ambient graph with child cap `k`, `D+E+C = k*R`, where `D` uses full ambient outgoing deficits, `E` incoming excess, and `C` actual outgoing crossing edges. | Infinite full-degree conservation, eventual regularity, and the sharper defect budget are not encoded. |
| [Binary avoidance](lean/SamuelAlexanderResearch/BinaryAvoidance.lean) | In the source manuscript's actual binary graph, an infinite path spelling its target forces that target to be eventually periodic. Therefore an aperiodic target is avoided from every starting vertex. | This formalizes the source's negative argument. It is not a new construction or the full positive theorem. |
| [Species bridge](lean/SamuelAlexanderResearch/SpeciesBridge.lean) and [binary population](lean/SamuelAlexanderResearch/BinaryPopulation.lean) | Exact ancestry, roots, finite children, increasing natural dates, finite date sublevels, functional edge labels, parent coverage, and infinitude. The whole avoiding graph is maximal specieslike, satisfies reflection, fails common ancestry, and avoids each aperiodic target. | Natural dates specialize the population model. The positive half of `specieslike_classification_of_positive` is an explicit theorem parameter. |
| [Two maximal cones](lean/SamuelAlexanderResearch/SpeciesCones.lean) | Exactly two inclusion-maximal sets satisfy IAP, convexity, common ancestry, and reflection: `C0={0} union {n>=2}` and `C1={n>=1}`. They are distinct, specieslike, and cover all vertices. | This is an exact classification inside this particular graph, not a general species theorem. |
| [General binary root obstruction](lean/SamuelAlexanderResearch/RootObstruction.lean) | Every `BinaryNatPopulation` has distinct roots `0` and `1`, so its whole graph cannot satisfy common ancestry. | At least two roots, not exactly two; the general `k`-label real-date statement is not encoded. |
| [Static mixing](lean/SamuelAlexanderResearch/StaticMixing.lean) | A common point of fixed rational planar regions belongs to every normalized weighted mix. A checked example proves the midpoint mix can strictly contain the intersection. | Rational vectors and explicit finite sums; no real convex-hull development or infinite lifeline/velocity theorem. |
| [Interval reachability](lean/SamuelAlexanderResearch/ThueMorseBound.lean) | For any Boolean coloring and target, all matching endpoints from `v>=1` form an exact integer interval. Its two boundaries follow deterministic trajectories; extinction is their coalescence. | The generic reduction does not by itself prove the Thue-Morse sharp bound or the equality family. See the [research note](research/thue-morse/INTERVAL-REDUCTION.md). |
| [Thue-Morse bits](lean/SamuelAlexanderResearch/ThueMorseBits.lean) | Actual binary digit parity, the even/odd recurrences, the full dyadic-block xor identity, and the required power-subtraction identities. | The sequence is defined recursively, not postulated to have the needed bit properties. |
| [Sharp Thue-Morse theorem](lean/SamuelAlexanderResearch/SharpThueMorse.lean) | Every matching path from `v>=1` satisfies `3*length <= 8*v-1`; a finite maximum exists; for every `n`, the maximum from `3*2^n-1` is `8*2^n-3`; these are exactly the equality starts. The actual bit identities, dyadic runs, coalescence lemmas, original-edge equivalence, and direct original-path prefix bound are checked. | Specific graph and target phase zero. The exact baseline `H(v)` first-hitting-time formula and real-coefficient optimality remain prose corollaries, not exported endpoints. |

## Definitions and assumptions that matter

The avoiding graph has no edge `0 -> 1`. For each `w>=2`, it has incoming edges from `w-1` and `w-2` carrying complementary labels. The first path edge must spell target index zero. These conventions are explicit in the source and independently checked in the graph, avoidance, and interval developments.

The final sharp endpoints include `SharpThueMorse.sharp_path_bound`, `sharp_maximum_exists`, `sharp_equality_family`, and `sharp_equality_indices`. The original graph is connected by `binary_edge_iff`, `binary_prefix_reachable`, and `binary_path_prefix_bound`; the result is not limited to an unconnected abstract recurrence. `RootObstruction.population_root_obstruction` quantifies over every `BinaryNatPopulation` and proves roots `0` and `1` and failure of whole-population common ancestry.

The counting model uses a functional `Option Nat` edge label, so one parent cannot provide several labels on the same edge. The fixed-gender model instead colors the source vertex permanently; this is a separate theorem with a separate hypothesis. Finitely supported child sets represent actual full outgoing counts in the infinite theorem. Its conclusion does not assume a family of finite prefixes or an aggregate count inequality.

The species definitions use strict ancestry in the ambient graph and weak connectivity inside the selected set. Reflection distinguishes infinitely many descendants in the ambient graph from infinitely many inside the set. Common ancestry requires a member of the set to be an ancestor of every other member. These are the conventions in Alexander's [2026 definitions](https://arxiv.org/html/2602.05274v1), not biological predictions inferred from the word "species."

## Statement review and attribution

The [population note](notes/POPULATION-COUNTING-FORMALIZATION.md), [binary proof note](notes/BINARY-AVOIDANCE-FORMALIZATION.md), [species note](notes/SPECIES-BRIDGE-FORMALIZATION.md), and [static mixing note](notes/STATIC-MIXING-FORMALIZATION.md) identify their exact definitions and limits. Separate reviewers inspected the binary offset argument, the graph-to-count and infinite-prefix assumptions, and the static region comparison. The coordinator inspected the composed species endpoint and the interval proof against their definitions. The [review record](verification/STATEMENT-REVIEW.md) records the material scope decisions.

The population framework and positive periodic theorem come from Alexander's [2013 paper](https://arxiv.org/abs/1212.0186). The avoiding construction and its offset argument come from the [2026 classification manuscript, Section 2](https://github.com/avg-netizen/biological-unavoidability/blob/main/paper.md). The manuscript already supplies its own negative formalization; the local Std implementation is independent code intended to compose directly with this repository's new graph modules. Neither that reimplementation nor the elementary counting deductions establish a literature-priority claim.

Alexander's [2026 Example 14(1)](https://arxiv.org/html/2602.05274v1#S6) already exhibits exactly one maximal common-ancestor cone per initial root in a related generational graph. Our graph has different edges, but its two-cone theorem instantiates that known phenomenon. The contribution here is a checked connection between the particular avoiding construction and these species predicates, not discovery of root-cone maximality in general.

## Reproduction and proof dependencies

Run from the repository root, with `lake` and `python` available:

```sh
lake build
python checks/audit_lean.py --output verification/formal-audit.json
python -m unittest discover -s checks -p 'test_*.py' -v
python checks/check_local_certificate.py
python research/thue-morse/interval_check.py
python research/thue-morse/sharp_check.py
```

The audit refreshes the library before reading the [endpoint manifest](verification/FormalAudit.lean), verifies the toolchain pin, rejects missing endpoint reports, and rejects every axiom outside `propext`, `Classical.choice`, and `Quot.sound`. It records source SHA-256 values in the [machine-readable receipt](verification/formal-audit.json). The source scan has no `sorry`, `admit`, project axiom declarations, or `native_decide`. Exact rational constant checks use `decide +kernel`.

All six unit tests and the finite diagnostics pass. In particular, the sharp diagnostic checks 18 complete trajectories, 8,140 individual advances, and 256 bounded baseline first-hit times, along with the stored scan's inequality and exact equality set. These are reproducible indexing checks; they do not replace the universal Lean proofs.

An axiom audit cannot detect a theorem whose conclusion was made a parameter. That is why the explicit positive premise of the conditional classification is called out above, and why statement review is separate from successful compilation. The [verification receipt](verification/FORMALIZATION-RECEIPT.md) records the current build and finite checks. The same checks run in [CI](.github/workflows/verify.yml); old CI receipts do not certify this patch.
