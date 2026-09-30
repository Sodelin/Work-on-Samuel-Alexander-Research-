# Local theorem and raw source tensor audit

Verdict: the inspected statements are soundly scoped, and I found no tensor normalization or symmetry defect. The complete arbitrary-arm canonical-theta theorem is now kernel checked. The raw N2 graph theorem is not yet a consequence of that local endpoint. This is an independent read-only audit of the parent-owned raw tensor files and a scope audit of this lane's own local theorem, not an independent reimplementation of every proof.

I read `RawNanuq.lean` and `SourceQuartetSymmetry.lean`, then traced their semantic dependencies through `SourceResolve`, `SourceQuartetRelation`, `SourceNetwork`, `GraphSwitchingFinite`, `QuartetSemantics`, `SourceCompositionBridge`, and the literal weighted definitions. I also inspected the exact statement and proof of `AnchorUnboundedSupport` and the successful latest axiom receipts.

## Raw tensor checks

- `ValidFour` imposes all six pairwise distinctions. `fourTaxa` is proved injective; repeated-label entries of `rawRho` are zero and are masked out of the source sum. They do not silently supply a quartet on duplicated taxa.
- `RootedBinary` contains finite graph incidence, degree, reachability, acyclicity, leaf-label, and LSA conditions. It has no supplied quartet resolver, desired decomposition, or symmetric tensor field. Parallel edge IDs remain distinct. The structure intentionally does not certify galledness, level, or outer-labeled planarity.
- `Switching.resolve` uses a proved unique concrete 2+2 edge-cut resolution of the actual selected graph. The finite switching type is nonempty, so the valid source mean never divides by the cardinality of an empty displayed set. Proof fields do not create extra choices: switching edge-code injectivity is proved.
- `rawQuartetMean` takes the image of the switching resolution map and then averages that finite set. Consequently it deduplicates quartet topologies before averaging. It does not average the switching multiplicities or the set of distinct whole displayed trees.
- `Resolution.swapCross` fixes the first-pair cherry and exchanges the two cross resolutions. `distinctMean_swapCross` is checked by kernel reduction over the finite resolution sets. The raw endpoint/witness symmetries then follow from actual edge-cut symmetries and resolution uniqueness. No symmetry assumption is inserted into `rawRho`.
- `rawNanuq_ordered_formula` uses the proved ordered/unordered pair identity with the repeated-label mask. The factor of two and constant term agree with the literal `sourceNanuq` definition. `rawNanuq_positive` proves strict off-diagonal positivity for at least three taxa; it does not prove triangle inequalities or circularity for arbitrary `RootedBinary` graphs.

## Exact local endpoint

`unbounded_source_full_theorem (t : Counts) (hlo : 1 ≤ t.total)` has no arm-length upper bound, compression premise, assumed displayed-support equality, or abstract local-positivity hypothesis. It proves circular decomposition, pseudometric laws, strict off-diagonal positivity, and exact positive coefficient support for the canonical path evaluator. `unbounded_weighted_exact_support` additionally quantifies over every strictly positive rational mass vector.

The support conclusion uses `displayedSplit`, whose Boolean search is proved equivalent to an actual switching edge with the required full leaf partition. Explicit canonical leaf positions prove every path cut circular; the boundary quartet criterion then proves support preservation under compression. Finite positive anchor witnesses are lifted by proved compressed-index surjectivity and order reflection. The only finite bound used is on the retained witnesses, not on the original theta. The finite support certificates are Lean proofs, and their hypotheses are actually discharged.

The lower bound is material. With no ordinary arm leaves there are two taxa: the source matrix is zero, while an edge still displays their split. The local exact-support theorem correctly excludes that case. Its three-taxon extension is algebraically proved, while the paper defines the global metric for at least four taxa.

The printed dependencies for `unbounded_support_exact`, `unbounded_weighted_exact_support`, and `unbounded_source_full_theorem` are exactly `propext`, `Classical.choice`, and `Quot.sound`. The lane source scan found no `sorry`, `native_decide`, new `axiom`, or `unsafe` shortcut. This audit did not alter any passed dependency source.

## Remaining source and graph obligations

The paper defines restriction through up-down paths, then suppression, and averages the distinct trees displayed by the induced quarnet. Its target class adds outer-labeled planarity, galledness, and level at most two to binary semi-directed LSA-rootable networks. Definition 4.1 and Theorem 4.7 concern at least four taxa; the proposed extension concerns the whole N2 class. These conventions were refreshed directly against [Definitions 2.1–2.5, equation (10), Definition 4.1, and Theorem 4.7](https://arxiv.org/html/2507.17308v2).

Three substantive links therefore remain distinct from the completed local result:

1. Prove the equality between the raw rooted-switching quartet set and the paper's semi-directed induced-quarnet displayed set, including root suppression, pruning, and degree-two suppression. Proving actual raw resolution existence does not by itself discharge this convention bridge.
2. Prove coverage: actual capped blobs of every eligible raw N2 network have the required canonical theta, one-cycle, or tree representation, with a compatible global circular order and positive taxon fibre masses. The canonical theorem itself is not a classification theorem.
3. Derive the actual per-anchor or quartet-localization composition identity from those raw graphs, including all bridge and small-port contributions, and prove both directions of global displayed-split lifting. The parent's conditional algebraic composition results are useful downstream results, but their graph premises must still be instantiated.

No statistical consistency, finite-data accuracy, coalescent identifiability, or NoAnomQ theorem is asserted by these local or raw tensor endpoints. The remaining distinctions are theorem-scope obligations, not discovered contradictions in the checked local result.

## Audited source snapshot

The following SHA-256 hashes identify the three principal files inspected; the parent checkpoint supplies the complete dependency manifest.

| File | SHA-256 |
| --- | --- |
| RawNanuq.lean | B6561AA41B7CF6596DB7EF006DCFC344B95E8A50A38021607F86642CF7AA144F |
| SourceQuartetSymmetry.lean | F2CC8AD0F73D2968A2560AB5B6BFD8FBCE3895FE38B85D41A5AE3AC798365F27 |
| AnchorUnboundedSupport.lean | 6F7558F3629BC3BFA880F4800FBF1F094CEA3242324F4DA030138C9744466FB2 |
