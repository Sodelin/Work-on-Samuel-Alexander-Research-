# Externally stated extension targets for the all-level NANUQ candidate

Evidence pass: 29 September 2026. This is a bounded research-target audit, not a novelty certificate or a claim that another open problem has been solved. Five distinct targets are ranked below. Two are literal open questions/conjectures; the others are explicit research directions. The broad questions have been narrowed below as our proposed targets, not attributed to the authors in that narrower form. A final targeted primary-source lead from the integration lane was included within this pass.

**Best next target: reduce quartet sampling in a NANUQ+ style inference procedure while proving preservation of the informative split structure.** This was explicitly proposed in August 2026. The all-level anchor certificate gives a direct algebraic starting point, but a useful sampling/coverage theorem and an inference guarantee are still missing. No additional external problem is already closed by the current files.

## Starting result and boundaries

The local input is `ALL-LEVEL-PROOF.md`, read with `ALL-LEVEL-STRUCTURAL-AUDIT.md` and `ALL-LEVEL-FINITE-AUDIT.md`. Conditional on accepting the assembled computer-assisted theorem, every two-anchor matrix of a finite binary, semi-directed LSA, outer-labeled-planar, galled bloblet has nonnegative circular coefficients in its embedding order, with no level bound. The independent finite receipt covers 84,076 ordered tree/duplication cases, 122 quartet systems and 24,667 coefficients. This audit did not rerun that computation.

The certificate records unions of displayed quartet topologies. It does not preserve joint realization of several quartets, switching multiplicities, inheritance probabilities, coalescent distributions, edge lengths or within-species sampling semantics. These distinctions control the rankings below. The present statement is for bloblets; a full-network application also needs the integration lane's composition bridge.

## Ranked targets

| Rank | Externally stated target | Kind and fit | Present disposition |
|---:|---|---|---|
| 1 | Reduce quartet sampling in NANUQ+ or replace collections of quartet queries with averages | Explicit 2026 algorithmic direction; strongest connection to anchor decomposition | A precise support-preservation obligation is available; no sampling theorem yet |
| 2 | Extend NANUQ+ to infer higher-level blob resolutions, at least partially | Explicit 2025 inference program; strong connection to all-level circularity | Requires an identifiable output, a reconstruction algorithm and statistical input bridge |
| 3 | Encode simple binary semidirected level-3 networks by quarnets after excluding a specified exceptional family | Literal combinatorial conjecture; precise, but a different observable and larger class | Requires network-valued restriction, an encoding proof and control of arbitrary competitors |
| 4 | Generalize circular-order information beyond outer-labeled-planar networks | Explicit source suggestion, motivated by indistinguishable nonplanar examples | Present adjacent-copy representation uses exactly the hypothesis to be relaxed |
| 5 | Does A-3blob hold under the displayed-tree model? | Literal open question; precise but weak fit to current machinery | Observation/sampling semantics and probability or metric information must be recovered first |

### 1. Fewer quartet queries with an inference guarantee

**Primary source and current result.** Dai and Molloy, *Is Level-1 Blob Reconstruction Under the Network Multispecies Coalescent Easy?*, WABI 2026, DOI [10.4230/LIPIcs.WABI.2026.1](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.WABI.2026.1). See Section 5, final paragraph, PDF page 16 (printed 1:16), for the proposed reduction of NANUQ+ quartet sampling/averaging. Sections 2-3 specify binary semidirected level-1 metric networks, independent-inheritance NMSC, generic quartet conditions, and a known tree of blobs. NetCS resolves blobs of degree at least five. Corollary 1, page 10, already supplies consistency and an O(n log n) quartet-query fast mode; Theorems 2-3 give probability bounds. Thus fast level-1 reconstruction is already established. [Published PDF](https://drops.dagstuhl.de/storage/00lipics/lipics-vol390-wabi2026/LIPIcs.WABI.2026.1/LIPIcs.WABI.2026.1.pdf)

**Our proposed bridge.** For a fixed bloblet N and a fixed correct circular order, write the current decomposition as

    d_N = sum_e M^e,

where e ranges over unordered anchor pairs. For a circular split S define

    H_S = {e : alpha_S(M^e) > 0}.

Choose anchor pairs E and positive weights w_e, and put D_E = sum_(e in E) w_e M^e. Nonnegativity immediately gives the exact criterion

    support(D_E) = support(d_N)
    iff E intersects H_S for every S in support(d_N).

Indeed each coefficient of D_E is a sum of nonnegative terms, and is positive exactly when at least one selected term is positive. This elementary conditional corollary is useful organization, not a separate discovery or a solution of the cited direction.

The substantive next task is to produce an efficiently selectable, substantially smaller E with a uniform coverage guarantee for a justified network class, without computing the full distance first. Computing all entries for E uses at most O(|E| n^2) quartet lookups before reuse, so a subquadratic anchor set could reduce the quartic lookup count. This is a bound on queries, not a full runtime or statistical guarantee. A comparison must acknowledge NetCS's stronger level-1 query bound.

A random version needs a proved lower bound on the fraction of anchor pairs in each H_S, followed by a simultaneous coverage bound; the current six-label certificate does not give that fraction. An adaptive version must count the queries needed to find the witnesses. Either route also needs a theorem connecting retained support to the intended identifiable output, and error control for estimated quartet classifications.

**Immediate falsification constraint.** A sparse sum can be only a pseudometric. Even for a source bloblet, retaining only anchor pair ab forces D_E(a,b)=0 by definition. As a separate illustration in the tree part of the certificate domain, a four-taxon tree with split ab|cd also gives D_E(c,d)=0 for that anchor. Thus positivity of retained coefficients neither separates all taxa nor establishes support preservation. Do not equate fewer nonnegative summands with a faithful reconstruction.

### 2. Consistent partial reconstruction of blobs beyond cycles

**Primary source and current result.** Allman, Banos, Rhodes and Wicke, *NANUQ+: A divide-and-conquer approach to network estimation*, DOI [10.1186/s13015-025-00274-w](https://link.springer.com/article/10.1186/s13015-025-00274-w). The Introduction's paragraph immediately before the paper outline proposes consistent inference of partial structure for blobs beyond cycles. The Discussion repeats higher-level resolution as future work. Its implemented target is cycle resolution from a tree of blobs and quartet summaries of gene trees; Theorems 3.10 and 3.14 identify the circular order and, for sunlets with more than four taxa, the hybrid from NANUQ/Modified NANUQ distances. ResolveCycle uses least squares, with a heuristic for large cycles.

**Our proposed bridge.** First specify the output: a circular split system, an observational equivalence class, or a particular network feature. These are different goals. The all-level theorem can justify fitting a circular distance for the stated bloblet class. It cannot identify a unique network from that distance.

A substantive narrow target is a consistent estimator of an explicitly defined all-level partial blob structure under a named gene-tree model. It needs: (i) a proved data-to-quartet-classification rule under that model; (ii) an injectivity or identifiable-quotient theorem for the requested structure; (iii) an actual algorithm and a noise/convergence argument; and (iv) a composition/rooting argument if outputs from multiple blobs are assembled. Exact equality of displayed-split support and distance support, if established by the integration lane, would help (ii) but still would not prove canonical-form uniqueness at every level.

**Prior-art boundary.** Holtgrefe et al., DOI [10.1007/s11538-025-01549-4](https://link.springer.com/article/10.1007/s11538-025-01549-4), Theorem 5.5 and Section 6, already prove level-2 canonical-form identifiability and sketch a consistent algorithm. Their level-3 circularity, parametric-distance, and whole-network metric conjectures are the parent project's existing targets, excluded from this count. No claim that an all-level circular matrix alone is a new consistent biological inference method is warranted.

### 3. The level-3 quarnet-encoding conjecture outside its exceptional family

**Primary source and exact target.** Huber, van Iersel, Jones, Moulton and Veenema-Nipius, *When are Quarnets Sufficient to Reconstruct Semi-directed Phylogenetic Networks?*, DOI [10.1007/s11538-025-01510-5](https://link.springer.com/article/10.1007/s11538-025-01510-5). Section 7's last paragraph conjectures encoding for all simple binary semidirected level-3 phylogenetic networks, excluding Figure 2's N1 and N2 and their extensions by inserting leaves on the a/b side in any order. In Section 4, simple means deleting all leaves leaves one blob. Encoding quantifies against every competing semidirected phylogenetic network on the same taxa, whereas weak encoding only compares members of the class. Theorem 6.2 proves level-2 encoding; Theorem 1.1 gives the level-3 counterexamples; Corollary 5.6 already recovers the blob tree at every level from quarnets. A quarnet here is a reduced induced four-leaf network under Sections 3-4, not a displayed quartet set. Definitions 2.2-2.3 also exclude parallel arcs and small blobs in phylogenetic networks.

**Our proposed bridge.** A first partial target could be encoding for the intersection with binary galled outer-labeled-planar bloblets, with the exact exceptional family checked rather than assumed absent. The paired-tip representation might organize how leaves attach to a generator. However, one would need to retain the full induced mixed four-leaf graph, including reticulation directions, instead of the screen's OR-mask of displayed trees. The finite certificate currently proves sign inequalities, not injectivity of this richer encoding.

Even a successful injectivity screen among bounded representatives is insufficient without a bound on a witness distinguishing two arbitrary-sized networks. The six-taxon bound concerns four entries of one anchor coefficient; it is not such a pairwise network-distinguishability theorem. Proving injectivity among planar galled level-3 networks alone would establish, at most, a weak encoding statement for that subclass. A full result must rule out competitors outside that subclass and potentially at higher level. Those are substantial new obligations.

This is the most concrete different combinatorial conjecture located. It ranks behind sparse sampling as a use of the existing machinery because its data and competitor domain both change. The targeted status search returned the source and related earlier reconstruction literature, but no verified resolution of this stated conjecture; that is not an exhaustive status certificate.

### 4. Circular-order information beyond outer-labeled planarity

**Primary source and current result.** Rhodes, Banos, Xu and Ane, *Identifying circular orders for blobs in phylogenetic networks*, DOI [10.1016/j.aam.2024.102804](https://www.sciencedirect.com/science/article/pii/S0196885824001362). In [author preprint v2](https://arxiv.org/html/2402.11693v2), Section 7's opening paragraphs suggest generalizing circular-order information beyond outer-labeled-planar networks because some nonplanar examples are indistinguishable from planar ones. Section 7.2 and Figure 9 give the relevant CF indistinguishability family. Theorem 5.3 already reconstructs an outer-labeled-planar blob's circular order from quartet information; Corollary 6.6 supplies a CF bridge under DT, NMSCcom, and NMSCind with NoAnomQ. These are existing all-level order results.

**Our proposed bridge.** One could seek an intrinsic class, strictly larger than the current embedding class, whose displayed-quartet system has a distinguished compatible circular order and whose anchor matrices remain circular in that order. This is our proposed formalization of the authors' suggestion, not their conjecture verbatim.

Opening pendant hybrids still suggests a repeated-label tree representation in a galled setting, but the adjacent-pair lemma currently comes from outer-face geometry. Without adjacency, a label need not occupy one consecutive block of tree tips; collapsing its occurrences then need not define a taxon order. The current restriction proof therefore cannot simply be reused. Moreover a generic galled network need not be outer-labeled planar.

The needed result is a source-network characterization guaranteeing a compatible order, then a restriction-closed finite witness domain and a proof of coefficient signs on that domain. A feature defined only by a convenient new representation would not by itself establish identifiability under the biological models in the source. Nonplanar examples sharing an existing planar quartet system would be illustrations of existing indistinguishability, not a fresh full solution.

### 5. Detecting a nontrivial 3-blob under the DT model

**Primary source, exact question and known comparison.** Allman, Ane, Banos and Rhodes, *Beyond Level-1: Identifiability of a Class of Galled Tree-Child Networks*, DOI [10.1007/s11538-025-01545-8](https://link.springer.com/article/10.1007/s11538-025-01545-8). Section 4 defines A-3blob: for an extended bloblet with an internal 3-blob, identify whether that blob is trivial. Section 5.6, immediately after Proposition 5.4, explicitly asks whether another approach can establish this under DT. Proposition 5.4 establishes it from quartet CFs for binary semidirected networks with generic parameters under NMSCind or NMSCcom and at least two samples per taxon. Definition 8 defines DT by displayed-tree inheritance probabilities. The question does not provide a new DT multi-sample protocol there. Section 5.5 distinguishes CF-only information from adding metric gene trees.

**Our proposed bridge and ranking.** Recover a precise observation experiment before attempting either a positive theorem or an impossibility witness. In particular, do not silently turn two opened occurrences of a hybrid taxon into two independently inherited within-species samples: the current construction chooses one occurrence per taxon in a displayed tree. It is a representation of alternative placements, not a sampling model.

The present theorem starts at four taxa, and its support-only summary discards the probability and branch-length information potentially relevant here. A new proof would need to characterize the appropriate DT observable for a trivial versus nontrivial 3-blob. A negative result would require identical distributions or the appropriate generic nonidentifiability condition under the same experiment, not merely matching unions of quartets. This is the most literally posed question in this list, but the weakest immediate use of the NANUQ machinery.

## Tempting claims excluded by the evidence pass

- **Unknown-level circular-order identifiability for outer-labeled-planar blobs:** already a principal result of Rhodes et al.; a new combinatorial metric supplies a different route or representation, not first identifiability.
- **Fast level-1 blob reconstruction from a known tree of blobs:** already addressed by NetCS in August 2026. Missing 3- or 4-cycle hybrid information must not be included in its guarantee.
- **Resistance metrics of arbitrary circular planar electrical networks are Kalmanson:** already proved by Forcey, [arXiv:2108.00550v1](https://arxiv.org/html/2108.00550v1), Theorem 4.2. Remark 4.3 shows the converse fails in general. Thus electrical realization is not automatic from the new circularity result. The broader topological questions in Forcey's Section 6 have no close bridge from the present coefficient certificate and were not promoted to targets.
- **All-level full network identifiability, or arbitrary higher-level canonical forms:** no such conclusion follows from nonnegative circular coefficients. Relevant positive theorems and explicit nonidentifiability examples already coexist in the neighboring literature.

## Recommendation and stopping point

The best concrete next experiment is the rank-1 witness-coverage problem: record, for each nonzero split coefficient, which anchor pairs witness it; try to prove a sparse selection rule that preserves a clearly named output. Keep this separate from the integration lane's full-support and parameter-domain theorems. A useful theorem must provide a selection rule and a bound, not merely the hitting-set reformulation above.

This pass found no different external question already settled by the current all-level candidate. It found an unusually direct, explicitly sourced algorithmic extension and four further avenues with visible gaps. Search stopped after one bounded pass; absence of a later paper in the retrieved results is not evidence of global priority or an exhaustive current-status review. No external write, publication, Git operation or proof-source edit was performed.
