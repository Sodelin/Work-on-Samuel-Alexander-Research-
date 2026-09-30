# Beyond NANUQ: bounded primary-source matching pass

Date: 29 September 2026. Budget: four search queries, at most three concrete targets, one bounded pass. Two targets are recorded below. No further external open problem was found that the present result already settles. This document supplements, rather than repeats, `EXPLICIT-EXTENSION-TARGETS.md`.

**Strongest actual match: a representation theorem for a restricted class of multi-labeled trees (MUL-trees).** This is more than an ancestry analogy: the occurrence tree is itself a MUL-tree. The restriction that each label occupies one contiguous block in a plane embedding must remain explicit. The extension from one/two adjacent occurrences to arbitrarily many contiguous occurrences is a pending mathematical step supplied by the integration lane, not verified here.

## 1. A circular representation of ambiguous quartet information in MUL-trees

**Classification:** recognized general structure; direct match on a restricted class; meaningful extension target; no exact externally posed open conjecture located.

**Primary prior art.** Deepak, Fernandez-Baca and McMahon, *Extracting conflict-free information from multi-labeled trees*, Algorithms for Molecular Biology 8:18 (2013), DOI [10.1186/1748-7188-8-18](https://link.springer.com/article/10.1186/1748-7188-8-18). The section “MUL-Trees and information content” defines an unrooted tree with a surjective map from leaves to labels, allowing repeated labels and internal degrees at least three. Its edge information requires all copies of the specified labels to lie exclusively on their designated side. Theorem 1 proves compatibility of this conflict-free information. Theorem 3 and Corollaries 1-2 establish the unique maximally reduced form; the reduction algorithm is quadratic in occurrence count. The Conclusions propose comparison with other reduction approaches, not our specific circularity question.

**Exact match and difference.** Let T be a finite plane binary tree, with leaf occurrences mapped onto at least four labels X. Assume every label's occurrences form a contiguous block in its cyclic tip order. Define Q_T(A), for each four-label set A, as the union of induced quartet topologies obtained by choosing one occurrence of every label in A. This is the same existential choice semantics as the current finite screen. In particular, its edge test asks whether a copy is present on each required side, not whether every copy lies there. The profile can retain two alternative quartet topologies, rather than discarding the conflicted four-label set.

The current one/two-occurrence certificate is already stated on all such adjacent-copy trees, a domain larger than the images of the original source networks. Thus a standalone MUL-tree corollary does not require another network-to-tree theorem. It does require explicitly carrying across the restriction proof, coefficient formula and certificate assumptions. This audit performed no fresh enumeration.

**Concrete proposed result.** For the one/two-occurrence class, publish the precisely scoped statement that the distance constructed from the distinct-topology profiles Q_T has a nonnegative circular split decomposition. Then, if the extremal-tip lemma is proved, strengthen it to arbitrary contiguous multiplicity by retaining only the first and last occurrence of each repeated label and taking their spanning subtree. The significant added statement would be that this at-most-2|X|-tip reduction preserves every Q_T(A), irrespective of the original occurrence count. The resulting coefficient reduction still uses at most six distinct labels.

The proposed reduction preserves a different observable from the known maximally reduced form. It is not automatically minimal, unique, or a canonical original-tree reconstruction. The distance need not recover the entire quartet profile merely because it was computed from that profile. Likewise, equality of positive metric support and the union of one-copy displayed-tree splits must be proved for the full MUL-tree representation domain if claimed there; a theorem stated only for network images is not enough.

**Best next packet.** State and independently prove the extremal-tip reduction for Q_T, then record exactly which split-support claims survive it. Compare that observable with the 2013 conflict-free observable on explicit examples. This can yield a general combinatorial result with a clear use outside NANUQ without advertising a solved external conjecture.

**Boundary.** A MUL-tree being drawable in the plane is insufficient: every tree is planar, whereas grouping all equal labels contiguously in a compatible tip order is an additional condition. The theorem must either take such an embedding as input or separately solve recognition of the restricted class. It does not yet apply to arbitrary multi-copy gene trees, and it supplies no model explaining why copies arose.

## 2. Selecting consistent prunings across multiple MUL-trees

**Classification:** recognized decision problem with current hardness results; related input objects; no direct theorem transfer and no new open-problem closure.

**Primary source and current status.** Hampson et al., *MUL-Tree Pruning for Consistency and Compatibility*, Algorithmica 88:58, published 8 July 2026, DOI [10.1007/s00453-026-01400-9](https://link.springer.com/article/10.1007/s00453-026-01400-9). The publisher's abstract defines MULSETPC as choosing a perfect pruning of each rooted MUL-tree to obtain consistent single-labeled trees. It reports NP-completeness even for two binary input trees with each label used at most twice, resolving the earlier fixed-number-of-inputs question. It also reports separate compatibility results and a tractable special case. Only the primary abstract was accessible in this pass; the full proof and exact theorem numbers were not inspected.

**Possible restricted bridge.** It is reasonable to ask whether supplying compatible contiguous label orders changes complexity for a precisely defined unrooted variant or a rooted variant with a specified root convention. That is our proposed restricted question, not an open question attributed to the 2026 authors. Their hardness statement alone does not show hardness with our block-order hypothesis, nor does our block hypothesis imply tractability.

The present summary records which individual quartets can occur under some choice. A pruning-consistency algorithm needs choices that work simultaneously across many quartets and across trees. The OR-mask discards those joint constraints. Nonnegative distances and identical quartet unions do not supply a common pruning. A useful extension would need a representation retaining compatible selections, together with a proved algorithm or hardness boundary for the restricted class. The six-label coefficient witness is not a bound on the size of an obstruction to simultaneous pruning. This is a lower-priority research direction until that information gap is addressed.

## Why this is not yet an ARG theorem

The primary model in Wong et al., *A general and efficient representation of ancestral recombination graphs*, DOI [10.1093/genetics/iyae100](https://doi.org/10.1093/genetics/iyae100), section “A general representation of ARGs,” has haploid-genome nodes and inheritance edges annotated with genomic intervals. Local trees are determined by those annotations. This section was read from the already archived primary full-text XML, including the formal (child, parent, interval-set) edge definition and Figure 1 discussion.

A contiguous interval along a genome is not the same condition as contiguous equal-label tips around a plane tree. Multiple local genealogies also need not arise by choosing one occurrence per label from one fixed occurrence tree. The present method omits genomic interval lengths, the joint arrangement of genealogies along the genome, and switching probabilities. Those omissions are not repaired by the abstract fact that both constructions describe ancestry.

An ARG application would first need a source-to-occurrence-tree theorem for an explicit ARG subclass that preserves the desired observable. No such theorem or exactly matching ARG open problem was identified in the four-query pass. Consequently, ARG reconstruction, general ancestry identifiability, and coding-language applications are not promoted to targets here.

## Disposition

Proceed with target 1 as the clear structural extension. Describe it as a theorem about ambiguous quartet information in MUL-trees with contiguous label blocks, subject to the remaining extremal-tip and support audits. Target 2 is a distinct but materially harder question about joint choices. The search found no basis for a universal MUL-tree theorem, an ARG inference theorem, historical priority, or a new external conjecture closure. No proof sources, Git state or external records were changed.
