# Full NANUQ formalization: obligations and scope

Started 2026-09-29 at the user's request. This directory is separate from the frozen computer-assisted proof packet. No completion claim follows merely from compiling these component modules.

Target: the extension of Holtgrefe et al. Theorem 4.7 from B2 to N2, with the actual uniform average over DISTINCT displayed quartet topologies. The conclusion is circular decomposability and support exactly the union of displayed-tree splits, for every finite binary semi-directed LSA-rootable, outer-labeled planar, galled network of level at most two and at least four taxa. Parallel edges and the two-port and three-port cases must be retained.

| Obligation | Current verified status | Remaining content |
|---|---|---|
| Distinct quartet semantics | `QuartetSemantics`, `ThetaSourceUnbounded`, and `SourceResolve` pass | Relate raw rooted switchings to the paper's semidirected/up-down restriction convention |
| Weighted anchors | Exact expansion, nonnegative coefficients, and invariance of positive support under positive masses pass | Apply to actual capped blobs after canonical coverage |
| Circular reconstruction | Exact reconstruction, unique split coefficients, pseudometric laws, mixture support, and ordered-subset restriction pass | Derive circular port orders from the actual planar embedding |
| Finite theta certificate | All 209 templates and 100823 anchor coefficients pass by kernel reduction; all 209 exact displayed-support certificates pass | No finite-template positivity gap remains |
| Unbounded theta reduction | Exact quartet and anchor compression, index/adjacency transport, arbitrary-arm positivity, and actual displayed-edge support compression all pass | No local compression or support-preservation premise remains |
| Canonical theta theorem | `CanonicalTheta.theta_source` proves circularity, pseudometric laws, strict off-diagonal positivity, and exact displayed-edge support for total >= 1; `theta_weighted` covers all positive rational masses; `theta_exact_quartet_mean` identifies the exact distinct-topology mean | Connect the canonical path evaluator to every eligible raw local graph |
| Raw graph foundations | Edge-indexed binary/LSA graph; actual bridge tree; positive bridge-side taxa; genuine finite switchings; unique actual quartet resolutions pass. `RawNanuq` constructs the actual numeric tensor and proves its symmetries and source normalization | Source convention bridge, outer-face representation, and full local blob construction |
| Rooted blob tree | Actual rooted orientation, injective degree-one taxon leaves, unique concrete port projections, their surjectivity, and strictly positive fiber masses pass | Three/four-leaf branching classification and quartet localization |
| Canonical coverage | Not yet proved | Derive tree/cycle/theta blob classification from raw degrees, gall/level/outer-face hypotheses, retaining parallel edges and small-port cases |
| Global composition | Mass algebra passes in `AnchorComposition`: one explicit per-anchor identity suffices; an independent mathematical audit supports the shorter route | Prove that anchor identity for actual raw blob projections; it is still an explicit premise, not a completed graph theorem |
| Circular lifting and global support | Exact mixture-support and interval-preimage algebra pass | Actual contiguous ports, split pullbacks, and both directions of global displayed support |
| Final source theorem | NOT COMPLETE | Source-class hypotheses must imply the conclusion without assuming canonical coverage, composition, circularity, or support |

The new direct anchor route was also tested against 70913 exact rational anchor entries on all 20 frozen multi-blob fixtures. That Python receipt is exploratory finite evidence, not a Lean certificate. The simple-edge fixtures do not test parallel edges. The new graph API preserves edge identities, so its proved graph lemmas do cover that representation.

`SourceScope.md` records the graph lane's exact convention boundaries. The original switching-average/discrepancy assembly remains available as a proved conditional algebra theorem; the direct anchor route may remove the need to formalize its tree-distance detour. No existing frozen proof or verification manifest was changed.

Every mathematical module must compile under pinned Lean 4.33.1 and Mathlib 0df444a360eaa60ab8c11dca51a86af692955474. Final declaration axioms must be printed. No `sorry`, ad-hoc axioms, `native_decide`, or trusted external Boolean result may certify a mathematical step. `decide` and proof-generating tactics are allowed because their resulting proof terms are checked by the kernel.

An explicit conditional algebra theorem can be useful, but its hypotheses remain open obligations until connected to raw networks. A structure with desired decomposition or positivity as fields does not close this target. The published unit-mass theorem must likewise be proved here, or be listed transparently as an external mathematical dependency; it cannot silently become an axiom.
