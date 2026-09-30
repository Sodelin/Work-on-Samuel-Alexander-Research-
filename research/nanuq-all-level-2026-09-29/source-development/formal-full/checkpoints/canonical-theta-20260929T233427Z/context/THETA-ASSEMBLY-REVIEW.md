# Assembly and restriction audit

Verdict: the reviewed assembled theorems are sound as stated. I found no missing arithmetic factor, implicit positivity assumption, or residual arm-length bound in the canonical-theta endpoints. This is a review of the stated formal interfaces and their implementation; it does not certify that the full raw-network class has already been connected to those interfaces.

Reviewed files: `AnchorUnboundedTheorem.lean`, `ThetaSourceUnbounded.lean`, `AnchorComposition.lean`, `CircularRestriction.lean`, `WeightedRestriction.lean`, and `ThetaWitnessSymmetry.lean`, together with the underlying anchor definitions and reconstruction normalization. The costly finite certificates were not rerun; their already successful kernel checks are unchanged.

`unbounded_anchor_nonnegative` has only valid finite indices and the two strict index orders as leaf hypotheses. Its compression-preservation input is discharged by `anchor_compression`, and the six-witness rank/index machinery supplies the finite bounds. There is no hidden original-size bound. `unbounded_weighted_circular` permits zero nonnegative masses, which is necessary for taxon deletion. `unbounded_weighted_support_matches_source` correctly strengthens this to strictly positive masses before asserting equality of positive supports. `unbounded_source_theorem` assumes one ordinary arm leaf, equivalently at least three total taxa, before claiming strict off-diagonal positivity.

`rhoFin_source` is an exact semantics theorem for four distinct valid taxa. It uses `quartet_resolves`, so `sourceResolution` does not silently fall back to a default topology on those inputs. The quartet list is deduplicated before averaging. The proof transports actual four-point choices, not merely signs of already calculated coefficients. `quartet_iff_separating_edge` now additionally identifies the executable test with concrete edge separation in the same root-path switching model.

The normalizations agree:

| Quantity | Formal normalization |
| --- | --- |
| `rho2` | Twice the uniform mean of cherry separation over the distinct quartet topologies |
| `rhoFin` | `rho2 / 2`, hence the source quartet tensor |
| `anchorMatrix` | Zero on the diagonal and anchor pair; one for one incident anchor; `2 * rho` outside both anchors |
| `weightedNanuq` | An upper-pair sum of `2 m_p m_q rho`, plus `(m_x + m_y)` times the mass outside x,y |
| `weightedNanuq_eq_ordered_anchor` | One half of the ordered anchor-pair sum; repeated anchors are explicitly zero |
| `circularAlpha` | The unhalved four-entry difference; a split's reconstruction weight is `circularAlpha / 2` |

`AnchorComposition.weighted_composition_of_anchor_identity` is a valid mass-counting theorem, including arbitrary rational input weights. Its anchor identity is a substantial explicit graph hypothesis. The theorem does not prove that identity for an arbitrary network, that its blobs have the required port projections, or that all tree junctions have been included. Treating the identity as already established by the algebra would be an overclaim. Summing by port fibres correctly retains repeated taxon-pair contributions, while `orderedAnchor` cancels repeated projected anchors.

`CircularRestriction.circular_decomposable_restriction` correctly asks for a strictly increasing inclusion of the chosen circular numbering. Its four-point inequality permits successor coincidences and the last-to-first wrap, so small retained subsets do not add an unstated cardinality assumption. It proves preservation of circular decomposability, not preservation of strict positive support on every old split.

`WeightedRestriction.weightedNanuq_restriction` gives the exact metric for the restricted quartet tensor by pushing the retained masses into the old index set. Unselected taxa receive mass zero. This is the appropriate operation for deleting a dummy taxon: restricting the old all-ones source distance would retain extra witness and incidence contributions and would be a different metric.

For a one-cycle component, deleting c2 from `theta(a,b,0,0)` leaves the order `c1, reverse(b-arm), a-arm`. The second switching bit affects only c2's terminal path, so the retained quartets have exactly two meaningful switching choices. This fact actually holds for every count tuple after excluding c2; the zero second-arm counts identify the intended one-cycle family. `ThetaDeletedHybrid.lean` is the separate executable proof of these assertions. At least three retained taxa, i.e. `a+b ≥ 2`, are needed for strict positivity of the resulting source metric. With two retained taxa the source formula is zero.

Remaining source-class obligations are genuine: correspondence between raw displayed network trees and the root-path evaluator; classification of admissible blobs into the canonical families; the graph-level anchor/composition identity; compatible global circular order and port intervals; and the advertised exact displayed support for the whole graph. The unbounded canonical support transfer is being assembled separately by the ordinal lane. None of these should be replaced by an assumed canonical presentation or by the name of a theorem.