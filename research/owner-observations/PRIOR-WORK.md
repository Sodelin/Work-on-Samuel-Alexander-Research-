# Prior-work comparison and observation boundary

Review date: 2026-09-27. This is a bounded primary-source comparison for Q2, not a worldwide priority search. The Q1 construction and its broader prior-art review belong to the separate genome-pedigree lane. Its exact source is pinned in DEPENDENCY.json.

## What the sources already establish

- [Thatte, Reconstructing pedigrees, Definitions 2.1-2.2](https://arxiv.org/pdf/1008.0153v3), PDF p.6: a diploid pedigree has a pairing of sequence vertices; the specified potential-parent graph determines non-extant pairing from common offspring. Our base graph contains realized transmission edges, which supply less information. Q2 assumes extra specimen co-ownership of labelled copies and does not contradict Thatte's determination rule.
- [Steel and Hein, Reconstructing pedigrees: A combinatorial perspective](https://www.math.canterbury.ac.nz/~m.steel/Non_UC/files/research/Steel_Hein.pdf), Theorem 2.1 and Remark 2.1: supplied sex-preserving subpedigree information affects reconstruction. The independent review checked these passages. This is prior evidence that observational labels matter; those subpedigrees are different from Q2's co-ownership samples.
- [Kirkpatrick, Non-Identifiable Pedigrees and a Bayesian Solution](https://arxiv.org/pdf/1602.08183), pedigree-identifiability framework and examples: genotype likelihoods can agree across distinct pedigrees under the specified models. This is established statistical non-identifiability. Q2 concerns a deterministic inverse map for one realised-history class; it neither equates nor separates those likelihoods.
- [Bauer, Monitorability of omega-regular languages](https://arxiv.org/abs/1006.3638): finite observations and finite witnesses for infinite-word properties are established formal-methods questions. This comparison uses the abstract's stated scope. The difference between eventual detection of a violation and finite certification of an always-negative infinite record is not a new general principle introduced here.
- [Official tskit data model](https://tskit.dev/tskit/docs/stable/data-model.html), Node Table and Individual Table, inspected 2026-09-27: the node's optional individual association and the individual table encode copy grouping explicitly. This is a concrete data representation for ownership metadata. Q2's oracle assumes that association and the matching of nodes to persistent copy lanes are accurate; phasing alone does not establish them.

The closest predecessor to the exact statement is the concurrently completed Q1 construction, especially its `query` interpretation in the written witness and `no_iap_decoder` finite-prefix theorem. The new deduction characterizes all static infinite sampling masks for the binary IAP target in that family. It is an elementary but sharp application of that construction. No source inspected states this exact mask criterion; that bounded finding does not establish priority or justify a broad novelty claim.

## The twin suggestion remains background

The user's twin-pair thought distinguishes similar sequence observations from organism identity. It is not a new proof or literature lane. Real monozygotic twins can differ in developmental and germline mutations: [Jonsson et al., Nature Genetics 53, 27-34 (2021)](https://www.nature.com/articles/s41588-020-00755-1). No repeated-twinning process, identical-germline assumption, relatedness coefficient, or twin-based observation-law equality is asserted by this packet.

## Evidence labels

Established prior mathematics: pedigree ambiguity, the importance of individual labels, and finite versus infinite monitoring distinctions. Reused checked result: Q1's diploid exact-edge-image construction and opposite IAP theorems. Candidate model-specific deduction: the exact odd-sampling criterion and its bounded-switch counterpart, subject to the packet's own proof gate. Speculation/outside scope: a noisy or adaptive genomic observation law, probability of the prescribed histories under a population process, and biological classification. No source warrants promoting those last items to proved results.
