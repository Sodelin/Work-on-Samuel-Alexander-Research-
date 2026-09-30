# Raw source-network formalization scope

Date: 2026-09-29. This is a source-fidelity and graph-interface report for the new `formal-full` lane. It does not revise the earlier frozen computer-assisted proof packet, and does not claim that the complete source theorem has already been formalized.

## Actual input, rather than an assumed decomposition

`SourceNetwork.RootedBinary` is a finite edge-indexed directed graph with an explicit root and injectively labeled taxa. It assumes the source's binary degree conditions, directed acyclicity, reachability from the root, and the least-stable-ancestor condition. Vertices other than the root and labeled leaves have degree type (1,2) or (2,1). The root has degree (0,2), each labeled leaf (1,0), and there are at least two taxa.

Edge identities are retained. Parallel edges are not collapsed to a `SimpleGraph` adjacency relation. This matters for the source's parallel two-cycles. Root suppression and conversion to the paper's semidirected convention are separate obligations; the root remains a degree-two vertex in the current raw graph.

The root's LSA condition is expressed by directed walks avoiding a candidate vertex: if a vertex lies on every root-to-taxon path, it is the root. No canonical blob type, blob decomposition, metric composition, circularity, split-support conclusion, or positive port-mass assumption occurs in the raw network structure.

`GraphGalls.GalledDetour` expresses the ordinary-edge detour joining the two parents of each hybrid while avoiding that hybrid vertex. Together with the two incoming hybrid edges it gives the source gall after simplifying the detour. The equivalence to the paper's *simple cycle* wording still needs a formal walk-simplification lemma. `LevelAtMost k` counts actual hybrid vertices in actual bridge-deletion components; it does not assume a theta representation.

## Completed raw graph results

| Module | Derived result |
|---|---|
| `SourceNetwork.lean` | Undirected and directed reachability, individual-edge deletion, bridges, actual blobs as nonbridge components, bridge endpoint separation, underlying connectedness. |
| `GraphGalls.lean` | Hybrid incoming edges are nonbridges under the gall-detour predicate; consequently all bridges are ordinary edges. |
| `GraphLeaves.lean` | Every vertex reaches a labeled leaf by finite acyclic induction; every forward-closed nonempty region contains a taxon; every nonroot vertex can be avoided by some root-to-leaf path using LSA. |
| `GraphCuts.lean` | Deleting one edge has at most two relevant connected sides; bridge sides are disjoint; the target side is forward closed; the root lies on the source side; both sides of every bridge contain taxa. |
| `GraphPorts.lean` | The actual leaf sets on the two sides form a disjoint exhaustive taxon partition. Both masses are positive and their sum is the number of taxa. |
| `GraphBlobs.lean` | The graph on quotient blobs and original bridge-edge IDs is a nonempty connected tree in the bridge characterization. Every quotient walk avoiding one retained bridge lifts to a walk avoiding that original bridge. |
| `GraphSwitching.lean` | Retaining all ordinary edges and exactly one parent edge at each hybrid yields a connected tree. Root reachability is derived by finite acyclic induction; the unique-incoming-edge cycle obstruction uses no axioms. |
| `GraphSwitchingDegree.lean` | Every actual switching has maximum undirected degree three and retains all original taxa as degree-one vertices. |
| `GraphSwitchingExistence.lean` | A default switching is constructed by choosing an actual incoming edge at each hybrid, proving the admission theorem is nonvacuous. |
| `GraphSwitchingFinite.lean` | Actual switchings are finite and nonempty. Their injective retained-edge Boolean codes ensure proof fields do not introduce duplicate choices. |
| `GraphSwitchingCuts.lean` | Every original bridge is retained under the gall condition, and its two vertex components, hence its taxon split, are exactly unchanged in every switching. |
| `GraphBridgeSplits.lean` | Actual bridge splits cannot cross as `ab\|cd` and `ac\|bd`, including in selected trees. This supplies the incompatibility part of the quartet-forcing argument. |
| `GraphQuartetExistence.lean` | Every quartet of distinct taxon leaves in every actual switching has an actual edge separating it 2+2. A lowest vertex with at least two selected descendants has exactly two; its incoming edge gives the split. This is derived from the raw graph, not assumed. |
| `SourceQuartetRelation.lean` | Each of the three resolution constructors has an actual edge-cut meaning, and bridge compatibility proves uniqueness. |
| `SourceResolve.lean` | The genuine raw switching resolution function is constructed with a proved specification. The distinct displayed quartet set and exact mean use that function. Any original bridge 2+2 split forces the resolution and exact mean in every switching. |
| `SourceFacts.lean` | Consolidated raw graph and actual-quartet prerequisite statements, separate from the desired metric theorem. |

`EdgeGraph.IsTree` is defined as nonempty, connected, and having every individual edge be a bridge. This is the usual tree characterization for an edge-indexed undirected graph, and excludes loops and parallel two-cycles. The result is derived for the actual quotient; a tree certificate is not an input field. The lifting and retained-bridge proofs use only `propext`; the other displayed axiom audits use subsets of `propext`, `Classical.choice`, and `Quot.sound`.

## Remaining source-to-theorem obligations

1. **Source convention bridge.** Prove correspondence between the raw rooted partner and the source semidirected network, including suppression of a degree-two root and invariance of displayed quartet topologies and relevant splits. Keeping the root internally may simplify the proof, but the final source statement still requires the correspondence.
2. **Outer-labeled planarity.** There is no graph-planarity certificate in the current input. A finite rotation-system/face certificate is a suitable raw representation, but its relationship to the source embedding and its induced circular order must be established. No canonical circular ordering may simply be assumed as a surrogate for this step.
3. **Gall wording.** Formalize walk simplification to relate ordinary detours to the source simple-cycle definition, including parallel-edge cases.
4. **Canonical coverage.** Derive the level-zero, level-one, and strict level-two local shapes from raw degrees, actual blob structure, gall conditions, level bounds, and outer-face conditions. The two-vertex cubic-core/theta classification and four-arm description are not yet kernel checked.
5. **Local networks.** Construct capped blob networks and prove they inherit the required raw source properties. Positivity of their actual port masses is now supported by `GraphPorts`; the local construction, cyclic port order, and source admissibility remain.
6. **Quartet localization and composition.** Actual switchings are now defined from raw edge selection and proved to be trees of maximum degree three, with all original taxon leaves retained. Existence and uniqueness of their edge-cut quartet resolutions are proved, and the actual finite distinct-topology average is defined. The raw bridge 2+2 forcing case is proved. Remaining steps are the product decomposition of switching choices by actual blobs, unique central-blob localization when four ports are distinct, the corresponding local restriction/surjectivity results, and the actual source metric composition. The selected spanning tree may contain unlabeled tips and degree-two vertices; the source convention bridge in item 1 must account for pruning and suppression and the paper's semidirected/up-down-path formulation. Uniform switchings must not be substituted for uniform distinct quartet topologies.
7. **Compression and support.** Relate the actual local graphs to the finite theta certificate by restriction/suppression, including switching restrictions and topology deduplication. Prove the graph meaning of local split support and its lifting to the full network, with small-port and level-one cases.

These are formalization gaps, not newly discovered counterexamples to the earlier mathematical argument. The checked foundations close substantive previously implicit steps: actual positive port masses, the actual blob quotient being a tree, admission of actual switchings as trees with the required degree bound and labeled leaves, and existence/uniqueness of actual raw quartet resolutions. The original-bridge forcing case now reaches the exact distinct-topology average. These results do not by themselves discharge the full B2-to-N2 conjecture in Lean.

## Verified entry points

`import SourceFacts` brings the checked graph lane together. `raw_graph_foundations` combines quotient-tree structure, ordinary bridge edges, and positive taxon partitions. `raw_quartet_foundations` supplies genuine actual-switching resolutions and nonempty displayed sets. `rawQuartetMean_of_bridge` is the checked 2+2 bridge case of the actual averaging semantics. The printed audits use only standard Lean axioms; no `sorry`, `native_decide`, user axiom, assumed quartet resolver, or assumed canonical decomposition is used.

## Pinned implementation notes

The checked compiler is Lean 4.33.1 at `C:/Users/Owner/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean.exe`. Imports come from the existing Mathlib checkout under `C:/Users/Owner/Documents/Codex/2026-09-24/alexander-formalization/real/.lake/packages/mathlib`. Only new files and their build artifacts in this directory are written.

Mathlib's source tree has an edge-indexed `Combinatorics.Graph` API, but its cached object files and a multigraph walk/bridge library were not present. The available `SimpleGraph` library would lose parallel edge identities. The small explicit API here uses `Relation.ReflTransGen` for edge-indexed reachability and standard quotient types. The finite well-founded argument requires `Mathlib.Data.Fintype.EquivFin` to provide `Finite.of_fintype`; importing `Fintype.Card` alone does not provide that instance in the pinned cache.

This report is intentionally a graph-lane inventory. Other agents' algebra and finite-certificate results are tracked separately in the shared obligation ledger.
