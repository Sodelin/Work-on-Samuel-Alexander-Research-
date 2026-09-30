**Final independent review of the NANUQ multi-blob extension — 29 September 2026**

**Verdict: PASS as a computer-assisted paper argument.** I have independently reviewed the completed [composition proof](../ordinal/COMPOSITION-PROOF.md), the source correspondence, the six-witness compression, the exact finite computations, and both directions of the global support argument. I find no outstanding mathematical gap in the proposed extension of Holtgrefe et al.'s Theorem 4.7 from bloblets to their full class N2. This verdict concerns the written proof plus the exact finite certificate. It is not a full Lean kernel certificate, a peer-review decision, or a certificate of worldwide priority.

The conclusion is precise: for every finite binary semi-directed LSA phylogenetic network that is outer-labeled planar, galled, and of level at most two, the source NANUQ distance is circular decomposable and its positive split support is exactly the union of the splits displayed by its displayed trees. The global leaf set has at least four elements. No substitution model, coalescent consistency result, finite-data recovery theorem, or biological identification claim follows merely from this combinatorial result.

Primary correspondence: [Holtgrefe et al., corrected publisher article](https://link.springer.com/article/10.1007/s11538-025-01549-4), also [arXiv 2507.17308v2](https://arxiv.org/html/2507.17308v2). The required published inputs are the definitions and canonical bloblet description, switching/restriction correspondence, circular coefficient inversion, and the unit-mass bloblet support theorem. The [January 2026 correction](https://link.springer.com/article/10.1007/s11538-025-01564-5) restores Figure 12b; it does not itself supply the multi-blob theorem. The separate [source audit](../source/source-audit.md) records the correspondence and the bounded acquisition limits.

**The logical chain that passes review.** All rho values below average uniformly over DISTINCT displayed quartet topologies. They do not average distinct whole displayed trees, and they do not count a quartet multiple times merely because several switchings produce it.

1. **Correct weighted local matrix.** On a blob's ports, with positive masses m, the zero-diagonal matrix is

       W_m(a,b) = 2 sum_{c<d outside {a,b}} m(c)m(d) rho_ab(abcd)
                  + (m(a)+m(b)) sum_{c outside {a,b}} m(c).

   If M^{cd} has entry 0 on the anchor pair, entry 1 for a pair meeting the anchors in exactly one label, and entry 2rho on a pair disjoint from the anchors, then direct expansion gives

       W_m = sum_{c<d} m(c)m(d) M^{cd}.

   Circular coefficients are linear, and their reconstruction identity holds for any symmetric zero-diagonal matrix. Nonnegative coefficients therefore supply the split decomposition directly; the argument does not assume an unproved triangle inequality for an anchor matrix. Once every anchor coefficient is nonnegative, all strictly positive masses preserve exactly the zero pattern, hence the support, of W at unit masses. Published Theorem 4.7 then identifies that support. Exact support of each individual anchor matrix is not an additional assumption.

2. **Finite compression is valid.** A circular coefficient of M^{cd} reads at most four boundary labels and the two anchors. Retain these labels and BOTH hybrid leaves of the canonical theta bloblet. Delete other ordinary arm leaves and suppress the resulting degree-two arm vertices, without changing retained arm order. For each of the four hybrid-edge choices, every queried quartet is unchanged under restriction. Deduplicated quartet sets and their normalization are therefore unchanged as well. The boundary pairs remain adjacent in the induced circular order. At most six ordinary leaves survive, so the coefficient occurs in a canonical theta with at most eight leaves.

   The parent and this audit check all 209 arm-count tuples with total between one and six, including four three-leaf cases. The source lane checks the 205 cases with total between two and six; its written reduction retains one extra original label when necessary to reach four leaves. These are consistent methods of closing the same small-case boundary. The zero-arm two-port case has the zero anchor matrix. There is no inference here from a large but incomplete arbitrary-network sample.

3. **The finite table is exhaustively and independently checked.** My [independent checker](independent_anchor_check.py) builds the four switched trees directly from the arm counts and extracts quartets by graph distances and the four-point test. It does not import the parent's split-extraction implementation. It checked all 100,823 anchor/circular-coefficient pairs across 209 templates, with zero negative coefficients. The exact histogram is 77,311 zeros, 19,440 ones, and 4,072 twos. It also verifies the anchor expansion at nonuniform masses on every template. Its [receipt](independent-anchor-check.json) is frozen below.

   The independently written source-lane checker agrees on all 100,787 coefficients in its 205 templates. The differences are exactly the four three-leaf cases: 36 coefficients, consisting of 24 zeros and 12 twos. The parent's exact rational checker records the same total of 100,823 checks, a completed 209-template sweep, and zero negative anchors. Thus the general local positivity statement has both a mathematical reduction and an exact complete finite verification.

4. **Level-one, tree and small-port cases close analytically.** On a level-one blob, the two switchings either give one quartet twice or two different quartets once each. Consequently the switching and distinct-quartet averages agree. The weighted metric is an average of weighted tree metrics, all compatible with the induced circular order. A tree's edge weights are positive products or sums of products of the nonempty branch masses. Two ports give W=0. Three ports give a star whose pendant weight at a is m(b)m(c)>0. Isolated ordinary degree-three tree vertices must be included as three-port blobs. Source-permitted parallel edges and two-cycles are covered by these arguments; the simple-graph implementation does not by itself cover parallel-edge presentations.

5. **The global composition identity is exact.** For each non-leaf blob B, its incident cut edges define nonempty external taxon blocks, of sizes m_B, and a projection pi_B from taxa to ports. Nonemptiness of a rootward port follows from the LSA condition; descendant ports contain leaves. These blocks partition the taxa. The proven identity is

       d_N(x,y) = sum_B W_{L_B}(m_B)(pi_B(x), pi_B(y)).

   The tree part is proved by assigning to each internal vertex the product of the masses in the other two branches for each incident edge. Grouping surviving degree-three vertices by their original blobs gives equality for every global switching. Suppressing degree-two vertices creates no new branching vertex. Local hybrid choices extend independently to global choices, so averaging gives equality for the auxiliary switching-weighted metric.

   The correction to the source metric then localizes exactly. A quartet with a 2+2 cut edge has one forced displayed topology and zero correction. Otherwise its reduced tree of blobs is a four-leaf star with one central blob and four distinct occupied ports. That blob determines both the distinct quartet set and the switching average. All other blobs contribute zero correction. Summing choices from two other port blocks supplies precisely the factor m_B(c)m_B(d). Adding these corrections proves the identity for the actual NANUQ metric. The difference between the two averaging conventions has been accounted for, not ignored.

6. **Circularity and exact support transfer globally.** In the outer-face leaf order, each port block is contiguous. A local circular split therefore lifts to a circular global split in one common order. Every local displayed split extends to a global switching, hence to a global displayed split. Conversely, an edge of a global displayed binary tree has an internal degree-three endpoint. This surviving vertex belongs to an original blob B and survives as a branching vertex in its local displayed tree. The local edge in the direction of the global edge induces the same taxon bipartition after the port blocks are substituted. This B has at least three ports. Therefore the union of lifted local displayed splits is exactly the global displayed-split union.

   Two-port blobs cause no missing positive split: their cut split is represented at an adjacent surviving branching blob. All local coefficients are nonnegative; every split in this union receives at least one strictly positive contribution. There is neither cancellation nor extraneous support. This completes the multi-blob theorem.

**Critical controls and what they establish.** The earlier [lane review](REVIEW.md) records an artificial circular family whose displayed split coefficient changes from 1 to 0 to -1 under repeated cloning. It is not an admitted N2 network counterexample. It correctly falsifies the shortcut that unit-mass circularity and support alone would imply arbitrary attachment closure. The final argument avoids that shortcut by proving anchor nonnegativity before varying masses and proving the literal global identity.

The parent implementation was inspected for source-class admission, quartet deduplication, coefficient normalization, and blob decomposition. No central mathematical defect was found. Its current receipt has `completed_template_sweep=true`, `template_count=209`, `anchor_status=PASS`, and 221 total rows: the 209 templates plus 12 cherry/graft controls. The earlier possibility of stopping at a negative anchor while issuing only a unit-metric status has been corrected: the sweep now completes and reports a separate explicit anchor status.

The additional [composition controls](../composition-controls.json) contain 20 actual admitted networks with up to 12 leaves and six hybrids, including 324 direct up-down restriction checks. They verify the exact composition and support on those cases. These are valuable implementation controls; the universal global conclusion comes from the symbolic proof above. I inspected their final receipt and coverage but did not independently rerun that additional parent suite. My complete independent rerun was the finite anchor table, where exhaustive checking is part of the proof.

**Frozen evidence.** Paths below are relative to the `nanuq` directory. Hashes identify the versions actually reviewed; later substantive edits should receive a new audit.

| Artifact | SHA256 |
|---|---|
| `ordinal/COMPOSITION-PROOF.md` | `762204fb95e3aa31a44506d9c113dd6f9559f21eaabb7fc811a2f8d09d3daa08` |
| `exact_networks.py` | `308a8751202151642f9919ca93564a67c442ea94008ba406fe2a024874994c6e` |
| `six-witness-search.json` | `481a1c4da63fe8ba0ce11f7b221564178e9ac86f6c93f1ef353f06c34941755a` |
| `composition-controls.json` | `9c61dea3724a7271c6555d41c310e29cd30a32894a1e9f069dccd9e7a71a3ea6` |
| `audit/independent_anchor_check.py` | `5f663e6be7acacdb7183dfc89950302b6999ccc252d2ff19cb7a106ce05da225` |
| `audit/independent-anchor-check.json` | `08d3c44426bf95cc82077a992d6275b9007a6fdab6da1262b5f8aa475fd4e006` |
| `source/anchor_audit.py` | `a0e9b3bf388f65d017fddb3da587d6956967689dfe17dc6026a12c0e5a212e49` |
| `source/anchor-audit.json` | `97dad56d5a0952d86c04872426c5e2fa3cbd178903b492ddae7f488e339465f` |

The final proof revision was also checked after its status, circular reconstruction explanation, and explicit level-one anchor argument were updated; the PASS verdict applies to the current hash recorded above. No further mathematical condition is being left to an unperformed experiment in this review. The remaining distinctions are evidentiary: the complete graph-theoretic argument and finite evaluator have not been checked by Lean, and the bounded source search does not establish priority. Generic coefficient lemmas proved separately in Lean do not change that boundary. Those facts should accompany any claim of the result, without downgrading the completed computer-assisted argument to a mere promising route.
