# Restricted pedigree reconstruction: a positive target with an explicit law

Owner: “Formalize Wong ARG and ancestry.” Status: source-reviewed literature connection and written finite target; no repository edits or Lean verification here.

The owner's existing counterexample establishes deterministic non-recovery from a retained finite genetic graph. It does not establish identical sequence distributions under a specified law. Keep compatibility with one observation, distribution identifiability, and high-probability recovery distinct.

## Additional primary results

Kim, Mossel, Ramnarayan, and Turner, [*Efficient Reconstruction of Stochastic Pedigrees*, arXiv:2005.03810v1](https://arxiv.org/abs/2005.03810v1). Theorem 6.1 (PDF p.33) gives high-probability recovery of an induced coupled subpedigree containing at least eta(alpha) of each generation as founder population N grows; eta(alpha) approaches one as the offspring parameter increases. Section 4.1 (pp.16–17) specifies graded monogamy, Poisson offspring with sufficiently large constant mean, independent half-probability block copying, unique founder symbols per block, B of order log N, and depth T = epsilon log N for sufficiently small epsilon. The reconstruction unit is a parental couple; extant observations are abstract single-symbol block sequences. The guarantee does not include ordinary phased diploid inference, mutation, realistic linkage, sequencing error, or continuous genomic recombination. Page 35 isolates first-generation reconstruction.

Mossel and Vulakh, [*Efficient Reconstruction of Stochastic Pedigrees: Some Steps From Theory to Practice*, arXiv:2204.04573v2](https://arxiv.org/abs/2204.04573v2), also published in [Pacific Symposium on Biocomputing 2023](https://psb.stanford.edu/psb-online/proceedings/psb23/mossel.pdf). Their tested finite simulations show weak recovery beyond two generations, with symbol reconstruction and inbreeding implicated. Belief-propagation and parsimony heuristics improve performance in those simulations. This does not refute the asymptotic theorem or prove general recovery for the heuristic. Sections 5–8 distinguish the empirical diagnosis and modified algorithm. The [author code](https://github.com/dvulakh/RecGen/tree/832d313b042fe74775d410d68bfebaeadef7f37c) was pinned but not executed.

These complement the owner's Thatte and Gravel–Steel reviews, which were not repeated. alphaXiv supplied selected source pages, not the entire proofs. This pass does not independently verify either paper's full mathematical argument.

## Finite first-generation target — our proposed specialization

This elementary target is motivated by the block model and REC-GEN's triples. It is not a novelty claim or a solution of general pedigree reconstruction.

Let a finite sampled child set be partitioned into monogamous families F_1,...,F_k, each with at least three sampled children. Families have disjoint parental pairs. In each of B blocks, every parent has a symbol distinct from every other parent's symbol. Each child copies one of its two parents' symbols with probability one half, independently between children and blocks. We observe exact block symbols for labeled children. Parent IDs and historical samples are not provided. There is no mutation, observation error, phase ambiguity, linkage between blocks, or inbreeding in this restricted model.

Create a 3-uniform hyperedge when three distinct children have a common symbol at any block. Return the maximal complete subsets of size at least three, placing one reconstructed parental couple above each subset.

**Proposed statement:** no mixed-family hyperedge is ever created. With probability at least max(0, 1 - M(3/4)^B), where M = sum_i binomial(|F_i|,3), the procedure recovers every sampled family and its parent-couple-to-child incidence graph, up to names of unobserved couples.

**Written argument:** a within-family triple agrees in one block exactly when all three copy the first parent or all copy the second: probability 2/8 = 1/4. Independence across B blocks gives miss probability (3/4)^B. Mixed-family agreement is impossible because the parental symbols are disjoint. A union bound over the M within-family triples ensures all these triples are observed together. On that event each family forms a complete hypergraph, while no cross-family subset can be complete. Since family sizes are at least three, the maximal complete subsets are exactly the families. The union bound does not require independence between triples.

The bound is sufficient and can be loose. This recovers one generation of sampled families. It does not recover individual parent names, assign a couple's symbols to its two members, include unsampled relatives, or cover smaller families. Unique observed founder symbols are a strong observation assumption, not something ordinary DNA sequences automatically provide.

## Integration and stopping condition

The proof owner can separate the deterministic hypergraph lemma from the finite probability bound. A bridge from its ARG/pedigree construction would then have to derive this observation law or replace it with quantified error assumptions. Shared founder symbols, overlapping parent pairs, correlated blocks and incomplete observation are explicit ways the guarantee can fail.

This target establishes restricted finite parentage information. It does not establish an infinite identical-ancestor property, ancestry convexity through omitted vertices, specieslike clusters, or biological species. Even a large induced subpedigree need not preserve ancestry paths through missing vertices. Those transfer conditions remain separate proof obligations.

The accompanying exact checker enumerates one-block triple cases, every two-block assignment for four siblings, and a two-family control. It checks concrete probabilities and reconstruction outputs. It is a finite mathematical illustration, not a general proof, Lean result, or biological benchmark. The bounded evidence pass stops with this written target and its source assumptions; proof implementation remains with the owner.
