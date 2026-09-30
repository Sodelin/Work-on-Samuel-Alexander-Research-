# Final source and local-theorem review

Date: 2026-09-29.

**Verdict: PASS for source correspondence, canonical theta coverage, finite compression, small-port and level-one cases, and admissibility of local blob networks. No remaining mathematical gap was found in these assigned obligations.** The explicit arguments below should accompany or be incorporated into the composition proof so its short inheritance and classification assertions are independently reviewable.

Reviewed document: `../ordinal/COMPOSITION-PROOF.md`, SHA-256 `8D6B9F8A21A91945AF5E6771AD18CF309625335EAE92915833ECF8B46077B951`. This review does not edit that document or the earlier frozen research packet. Another agent owns the independent global algebra/support audit; this verdict does not substitute for that audit or for a Lean kernel certificate.

## 1. Exact match to the source question

The [corrected primary article](https://link.springer.com/article/10.1007/s11538-025-01549-4), immediately before Theorem 4.7 and in Section 6, asks to extend circular decomposability and exact displayed-split support from its bloblet class B2 to the full class N2. The reviewed proof uses the same binary semi-directed networks admitting rooted LSA partners, at least four taxa, outer-labeled planarity, galledness, and level at most two. It also preserves the uniform average over **distinct** displayed quartet topologies in Definition 4.1.

There is no unnoticed extra assumption of cycle-freeness, strict level two, absence of parallel edges, or a single nontrivial blob in the final statement. The target is the full stated B2-to-N2 extension. It does not include the paper's separate level-three or parametric-distance questions, nor does it establish statistical performance on finite sequence data. Section 6's observation about potentially relaxing conditions on two- and three-port blobs is broader than the formal N2 target; it is not needed here.

## 2. Every local network has the required source admissibility

Let B be a non-leaf blob and cap every incident cut edge by a newly labeled port leaf. The following details justify the construction in the proof.

**Every port mass is positive.** In a rooted partner, a bridge directed away from the root leads to a component containing a leaf: follow outgoing edges in that finite acyclic component. If a rootward component contained no taxon, every root-to-taxon path would cross the bridge into the other component. Its descendant endpoint would then be a common stable ancestor strictly below the root, contrary to the LSA assumption. If the suppressed root lies on the bridge, both directions away from it lead to taxa. The blob tree therefore has no unlabeled terminal blob; each non-leaf blob has at least two ports. The components at its ports partition the global leaf set.

**Binary degrees and hybrid edges are preserved.** A bridge cannot be a hybrid edge in this galled class: every hybrid edge lies on the gall witnessing its hybrid's two incoming edges. Thus capping bridges replaces only non-hybrid edges. Every vertex of B keeps its degree, every new port is a leaf, and every hybrid remains with both incoming edges in B. An isolated non-leaf tree vertex becomes a three-leaf star.

**There is an actual rooted LSA partner of the local network.** If the original root lies in B, retain the rooted restriction and cap outgoing attachments. A proper descendant dominating all port leaves would dominate all original taxa, contradicting the original root's LSA property. If the original root lies outside B, there is one rootward port. Subdivide its pendant edge by a new root, direct one root edge to that port leaf and the other into B, and retain the original orientations inside B and toward the other ports. The entry vertex is a tree vertex because the entry edge is not hybrid. All required in/out degrees hold, the graph remains acyclic, and the root is the LSA because its two children separate the rootward port leaf from all other ports. The same construction applies when the original suppressed root lies on a bridge.

**Planarity, galledness, and the level bound persist.** Capping the attached components leaves the original planar embedding of B. Every port is incident to its outer face: an attachment lying wholly inside a bounded face would have contained original taxa off the global outer face, which is excluded. Every gall is contained within its blob, so the same gall works after capping. No hybrids are created or lost inside B. The capped network is therefore a source-admissible bloblet whenever it has at least four ports, and the same local graph construction is admissible with two or three ports as well.

This is stronger than merely checking degrees of an arbitrary partly directed graph: it supplies the rooted LSA partner required by the source's definition.

## 3. The canonical theta templates cover all strict level-two bloblets

Here is a structural justification independent of the simulation family.

Delete the pendant leaves of a strict level-two bloblet and examine its remaining bridgeless core. In a binary graph, a bridgeless core has internal degree two or three. A core vertex of degree two has exactly one pendant leaf in the bloblet. Galledness places every hybrid among these articulation vertices; therefore each of the two hybrids has its own pendant leaf.

The core has cycle rank two. This follows either by Euler counting in a rooted partner or from the ordinary binary-network identity that cycle rank equals the number of hybrids. Suppress core vertices of degree two. The resulting bridgeless cubic multigraph has exactly two vertices: for a connected cubic core, `cycle_rank=1+V/2`. Its three edges must be parallel edges between those two vertices. The alternative of a loop at each vertex joined by an edge would have a bridge. Thus the unsuppressed core is a theta: three internally disjoint paths joining two tree junctions.

The two hybrids lie on different theta paths. Otherwise every cycle through either one's incoming pair would also contain the other hybrid's incoming pair, violating galledness. Both hybrid-bearing paths must occur on the boundary of the unbounded face, since each has a pendant labeled leaf. The remaining theta path is internal to the embedding. It cannot contain any vertex with a pendant labeled leaf, so it has no degree-two core vertices and is exactly the central edge.

The two outer paths have one hybrid each and may have arbitrary numbers of ordinary pendant leaves on either side of the hybrid. These are precisely the four ordered arms A1,B1,A2,B2. Empty arms are allowed. This proves coverage by the canonical theta family, including three-cycles and all empty-arm degeneracies. Parallel two-cycles occur in the lower-level/two-port cases; they are not an omitted strict level-two theta shape.

## 4. Finite compression preserves the tested quantity

An anchor coefficient depends only on its two anchors and the three or four boundary leaves of the circular split coefficient. Keep those named leaves and both hybrid leaves. Delete other ordinary arm leaves, suppressing each vacated degree-two arm vertex without changing the order of retained leaves along an arm.

For every fixed switching choice, this operation is exactly restriction of the switching tree followed by suppression. Tree restriction is transitive, so every quartet on retained named leaves is unchanged. This is true separately for all four switchings, including choices that happen to yield the same quartet. Taking the set of their outcomes therefore preserves the distinct-topology average; no multiplicity substitution occurs.

The two boundary adjacency relations survive because there were no original labels between either adjacent pair. Consequently the same circular coefficient, with the same coincidences among names, exists in the reduced network and has exactly the same value.

At most six ordinary arm leaves remain. For four or more retained taxa, the 205 templates with ordinary-arm sum from two through six suffice; my earlier independent audit checked all 100,787 coefficients on those templates. Retaining only three taxa is harmless: there is no four-distinct-label rho term, and the anchor matrix is defined entirely by 0 and 1. I independently ran the four additional templates with ordinary-arm sum one in this review. They contribute 36 coefficients: 24 zeros and 12 twos. This gives exactly the parent's totals of 209 templates and 100,823 checked coefficients, with no negatives. The all-zero arm tuple has two leaves and an identically zero sole anchor matrix.

The reduction needs no unproved inference from the support of a restricted split to a full split. It is used only for coefficient nonnegativity. Exact support for positive masses then follows from the unit-mass source theorem and the positive anchor combination, as the composition proof states.

## 5. All small-port and level-at-most-one cases are covered

**Two ports.** W is identically zero, and no four-taxon quartet term exists. The local displayed tree has an edge, but the proof correctly does not assert positive support for this two-port local matrix. A global split represented through a chain of two-port blobs must receive its contribution at a branching blob; the global support audit handles that step.

**Three ports.** Regardless of the local reticulation presentation, every displayed tree simplifies to the same three-leaf star. W has pendant lengths `m(b)m(c)` at a and the two analogous positive products. Its support is exactly the three trivial port splits. A three-port anchor is the same star with just one positive pendant length, equal to 1; its sole positive alpha is 2. This covers strict level-two three-port residuals as well as level one and ordinary tree vertices.

**Level one with at least four ports.** There are only two local switchings. On any quartet, they either agree or produce two distinct topologies; uniform-distinct and uniform-switching averages therefore coincide. Hence W is the average of two weighted tree metrics in the same circular order. All their tree-edge lengths are positive for positive masses and at least three terminals, so their average has precisely the union of their supports.

The stated anchor lemma itself also follows, if desired explicitly. Each tree-edge weight in Section 1 is a polynomial in `m(c)m(d)` with nonnegative coefficients. Extracting one such coefficient gives a tree anchor represented by nonnegative tree-edge weights. A level-one anchor is the average of its two tree anchors. Thus its circular coefficients are nonnegative. This supplies a direct proof of the all-anchor wording, rather than relying only on weighted positivity.

**Level zero.** A non-leaf singleton blob is trivalent and is already covered by the three-port star case. More generally, the tree identity gives the required weighted and anchor statements directly.

## 6. What this verdict establishes, and what it does not

The final mathematical statement has the source's full intended scope. The canonical finite family is exhaustive for the strict level-two local obligation; small-port and level-one cases do not hide an untested family; and each local graph actually meets the source's admissibility conditions. The source-definition and local-lemma audit gate can be marked passed on the basis of this report and the preserved exact evaluations.

**Exact remaining gap in this assigned lane: none.** For a self-contained final exposition, include or cite the rooted-local-partner construction and the theta-classification argument above; these supply details that the reviewed draft abbreviates. The finite evaluator remains an ordinary exact-arithmetic computer-assisted certificate, not a Lean proof. That difference is a verification-level limitation, not an additional missing mathematical case.

The global composition identity, discrepancy localization, and exact lifted-support conclusion are being reviewed independently in the other lane. Once that audit is accepted, the local condition described as conditional in Section 7 is discharged by the reduction and certificate reviewed here. No claim of external peer review, publication priority, biological identifiability beyond the source framework, or level-three generality follows from this audit.

## Final revision alignment — approved 2026-09-29

Re-read the amended `../ordinal/COMPOSITION-PROOF.md` with SHA-256 `762204FB95E3AA31A44506D9C113DD6F9559F21EAABB7FC811A2F8D09D3DAA08`.

**Final revision approval: PASS.** The three amendments agree with this source/local review:

1. Section 4 now explicitly uses the circular reconstruction identity for any symmetric zero-diagonal matrix. With the stated boundary-gap convention, the split coefficient is alpha/2. Consequently nonnegative anchor coefficients give a split-metric decomposition without assuming a triangle inequality beforehand. This is the appropriate algebraic use of the identity underlying source Proposition 2.8.
2. Section 5 now proves the level-one anchor statement itself by extracting nonnegative monomial coefficients from tree-edge polynomials and averaging the two tree anchors. This is exactly the argument approved in Section 5 of this review.
3. The local finite lemma is marked established by the compression proof, 209 templates, 100,823 exact checks, and the independent reviews. Those counts and that scope agree with the preserved evidence reviewed above. The updated theorem wording accordingly discharges the former local condition.

The composition identity, global support argument, network class, and distinct-quartet metric are unchanged in this revision. No new source/local gap was introduced. This approval is tied to the final hash above, superseding the earlier proof hash for revision alignment; the initial review and its detailed mathematical justifications remain valid. It preserves the stated computer-assisted, non-Lean verification level and the separate global-audit responsibility. No further research or edits were performed for this alignment pass.
