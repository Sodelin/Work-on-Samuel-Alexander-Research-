# Independent statement review: first integration stage

Historical record. The subsequent [gap-closure review](GAP-CLOSURE-REVIEW.md) supersedes the remaining-gap status below while preserving these original reviews.

Review date: 24 September 2026 (host local date). These reviews concern the formal statements and mathematical interpretation; the separate axiom audit concerns their proof dependencies.

Work used separate file owners for population counting, species geometry/composition, interval reachability, and the coordinator's avoidance/algebra/integration work. The other active research task handled source interpretation and separate exploratory notes. No two implementation lanes edited the same Lean module.

| Reviewed material | Independent check | Disposition |
|---|---|---|
| `BinaryAvoidance.lean` | Species reviewer compared the actual edge convention, arbitrary starting vertex, natural subtraction bound, proved offset stabilization, and both parity periods with Section 2 of the source manuscript. | No discrepancy found. Composed with independently proved population and species properties. |
| `PopulationCounting.lean` | Species reviewer inspected actual adjacency, finite parent coverage, child-support caps, generated infinite prefixes, root bounds, and finite ambient critical conservation. | No circular count assumption found. Root flags agree with parentlessness for $k>0$, as forced by $d<k$; the note treats $k=0$ separately. |
| `StaticMixing.lean` | Counting reviewer checked the weighted constant-vector identity, witness construction, midpoint example, and correspondence to the corrected static-intersection comparison. | No blocking issue. Added a note that duplicate list indices reuse their chosen point; no equality with the independent occurrence-wise nonconvex mixture is claimed. |
| `BinaryPopulation.lean` and `SpeciesCones.lean` | Coordinator inspected the forgotten-label equality, full negative conjunction, exact cone membership, CA containment argument, and maximality proof. The other research task independently derived the same two-cone classification. | Exact graph-specific bridge accepted. The positive classification theorem remains an explicit parameter and is not presented as an unconditional result. |
| `ThueMorseBound.lean` | Coordinator inspected the actual reachable-path recursion, missing root edge, interval propagation, lower start bound, and one-step shift between last surviving depth and extinction. Independent interval computation agrees with the pre-existing set engine. | Universal interval theorem accepted. Numerical Thue-Morse conclusions need their own argument. |

The checked graph uses natural-number birthdates. The conversion from arbitrary real birthdates to a natural ordering, the positive unavoidability theorem, and the infinite full-degree critical identity remain outside the encoded statements. Keeping these gaps explicit is part of the review result.

The subsequent sharp Thue-Morse proof was written by the interval researcher, independently rederived by the counting reviewer, and read by the coordinator. Review checked all five lower-trajectory runs, the dyadic descent, the $r=1$ and $q=1$ cases, monotonicity for every positive start, and the one-step shift from coalescence to maximum length. The bits reviewer then supplied an actual recursive sequence and proved its full dyadic-block identity; the counting reviewer formalized the trajectory and sharp endpoints. The conclusion is a proof of both repository conjectures, with separate finite diagnostics retained only as corroboration.

The whole-graph CA obstruction was independently proposed by the other research task and formalized for the binary natural-date model. The coordinator checked that the statement is universal over `BinaryNatPopulation`, and that it asserts at least two roots rather than exactly two.

The final sharp development received a second statement audit from the species reviewer after the original-graph bridge was added. The reviewer checked `binary_row_eq`, `binary_edge_iff`, the edge-count meaning of path length, the direct finite-prefix bound, existence and greatestness of maxima, and the complete equality-set theorem. No trajectory conclusion is a premise of the sharp endpoints; the positive-start restriction is explicit. This final audit found no model shift or missing universal quantifier.

No novelty verdict follows from this review. Source priority and independent external mathematical review remain distinct from local agent review and Lean verification.
