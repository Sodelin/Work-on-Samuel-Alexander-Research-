# Ancestral-material restriction and exact sample-path preservation

## Source and scope

This module addresses a precise part of Yan Wong et al. (2024), [*A general and efficient representation of ancestral recombination graphs*](https://doi.org/10.1093/genetics/iyae100), especially the discussion of ancestral material and sample resolution on journal pages 3–4. The [published PDF](https://www.pure.ed.ac.uk/ws/portalfiles/portal/458588307/iyae100.pdf) includes an extra cover page.

The paper distinguishes inherited material that reaches designated samples from material that does not. Appendix G describes further simplifications, including node removal and edge rewriting. Our operation removes nonancestral edge material at each locus. It preserves original node identities and ancestry paths; it does not implement unary suppression, truncate above local MRCAs, or reproduce every option of tskit's simplify algorithm. In particular, Figure 3's removal of the grand MRCA is outside this operation.

Implementation: [AncestralRestriction.lean](../lean/SamuelAlexanderResearch/AncestralRestriction.lean). This is a new formal derivation from an elementary relation model, not a claim of mathematical novelty or independent biological validation.

## Definitions

Let R be a directed parent-to-child relation and S a predicate marking sample vertices. Reach R a b is the existing nonempty-path relation.

- Ancestral R S a means that a is itself sampled, or that there is an original R path from a to some sampled vertex.
- Restrict R S a b means that R a b and the child b is ancestral.
- For a family of relations R indexed by genomic location i, AtLocus R S i applies Restrict separately to R i.

The direction is ancestor to descendant. When reading data expressed with child-to-parent edges, reverse the orientation before applying the interface.

No desired preservation theorem is assumed in these definitions. In particular, Ancestral is evaluated in the input graph. The theorem that this predicate is unchanged in the output graph is proved subsequently.

## Verified mathematical targets

Checked with the pinned Lean toolchain by the root task: the standalone module compilation exited successfully, and all 11 printed endpoints used only permitted standard axioms or no axioms. This check is separate from the final aggregate repository audit. The checked source SHA-256 is 9A8C8F611CCAC15DDD737188BF8F5A65057D01BEFA52C597F2C3C7508FDD8AC1.

| Endpoint | Exact conclusion |
| --- | --- |
| locus_sample_path_iff | For any fixed locus and designated sample s, a path from a to s exists after restriction exactly when it existed before. |
| ancestral_restrict_iff | The sample-ancestry predicate computed in the restricted graph equals the original predicate. |
| restriction_resolved | The child of every retained edge is ancestral in the resulting graph itself. |
| restriction_idempotent | Applying restriction twice with the same samples changes no edge. |
| restriction_mono_samples | Increasing the sample set can only add retained edges. |
| restriction_nested | Restricting to S and then to a subset T gives precisely the same edges as restricting directly to T. |
| restriction_union_iff | Restriction to the union of two sample sets is exactly the union of the two separately restricted edge relations. |
| erase_restriction_sound | Any edge retained at some fixed locus is retained if locus labels are erased first. |
| erasure_restriction_do_not_commute | The converse fails on an explicit two-edge acyclic example. |
| indexed_recovery_iff | All original indexed edges are recovered from the retained indexed relations exactly when every original edge already carries ancestral sample material. |
| raw_graph_not_identified_by_sample_relations | Two different raw indexed graphs have identical retained indexed sample relations. |

The preservation proof follows the actual path inductively. If the final vertex is ancestral, then each preceding vertex is ancestral, so every edge along that path passes the retention condition. Conversely, every retained edge is an original edge. The nested-restriction theorem uses the fact that every path to a smaller-set sample was preserved by restriction to the larger set.

These are relation equalities and reachability theorems. They preserve node identity and every original edge on any sample-ending path, including edges incident to unary vertices. They do not assert equality of an unspecified tree-shape encoding.

## Why genomic labels must survive sample resolution

The counterexample uses two genomic locations, represented by false and true:

| Location | Original edge |
| --- | --- |
| false | 0 to 1 |
| true | 1 to 2 |

The only sample is vertex 2. At location false, vertex 1 is neither a sample nor an ancestor of a sample at that location, so the edge from 0 to 1 is discarded. At location true, the edge from 1 to sample 2 remains.

If the locations are erased first, the graph has the path from 0 through 1 to 2. This mixed-location path causes the edge from 0 to 1 to be retained. Thus erasing locations before ancestral-material resolution retains an edge that fixed-location resolution correctly removes.

This is a strict, Lean-expressed limitation on the proposed bridge to an unlabelled organism graph: erase_restriction_sound supplies one direction, and erasure_restriction_do_not_commute refutes the unconditional converse.

## Exactly when full indexed reconstruction is possible

A sample-retained indexed relation does not automatically determine its raw input. Define VisibleTail to contain only the true-location edge from 1 to 2. Restricting either VisibleTail or the original two-edge SplitLocus graph to sample 2 produces the same relation at every locus. Their original false-location edges differ. Both graph relations increase the natural-number time coordinate, so this failure does not rely on cycles.

The recovery criterion states the exact missing hypothesis: for every locus, every raw edge's child must already be ancestral to a sample at that locus. Under that condition, restriction retains all raw indexed edges. If complete indexed recovery holds, the condition follows directly for each recovered edge.

This clarifies the boundary relevant to reconstructing a gARG from local relations: one must retain the indexed relations with node identities and ensure the original graph has no omitted nonancestral material. Recovering interval encodings from equal pointwise incidence additionally requires an extensional or normalized interval representation; raw interval lists need not be unique.

## Applying the theorem to an interval gARG

The theorem is polymorphic in both the vertex type and the genomic-location type. To instantiate it, define R i p c to mean that the original edge from p to c carries location i. The fixed-locus theorem then preserves precisely the ancestry paths to selected samples at that location.

To obtain a concrete output in the finite interval-record format, further work must show that each retained set of locations can be represented by an admissible finite collection of disjoint intervals, and that its membership relation equals AtLocus. Endpoint-cell methods can establish that result for a finite interval input. Merely deleting a whole record whenever part of its interval is nonancestral would not implement this definition: individual records can require trimming or splitting.

The generic theorem requires no finiteness or acyclicity. A finite, acyclic input remains finite and acyclic under edge deletion, but a faithful interval model should expose those invariants independently. Unique parentage at a location, when supplied by a concrete input, is inherited by a subrelation; it is not manufactured by this restriction.

## What this resolves for the Alexander connection

This formalization supplies a justified sample-resolution stage before any genome-to-organism projection: it proves which fixed-locus sample ancestry facts survive and which information is lost if genomic labels are discarded too early. Existing HistoryProjection theorems can then project retained paths under their explicit per-edge biological compatibility hypothesis.

Nothing here identifies finite genome graphs with an infinite Alexander population, proves a specieslike-cluster axiom, or establishes graph self-similarity. Those claims require separate definitions and proofs. Nor does the module formalize statistical ARG inference, stochastic recombination models, mutation likelihoods, or all of Wong et al.'s paper.