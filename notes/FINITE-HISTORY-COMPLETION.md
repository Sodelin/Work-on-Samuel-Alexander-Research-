# Finite history and infinite species properties

Status: `FiniteHistoryCompletion.lean` individually checked with Lean 4.33.1; all seven printed endpoints use only the permitted standard axioms. Final aggregate receipt is recorded separately.

Theorem `finite_history_does_not_determine_species` starts with any graph on a finite natural-number prefix whose edges respect that ordering. It constructs two graphs on all natural numbers. Both preserve the input edges exactly and preserve all directed paths with an endpoint in the old history. Both have increasing birth indices, finite children, finitely many roots, infinitely many vertices, and connected underlying undirected graphs.

In the first completion every old vertex connects to one new vertex, followed by a single infinite chain. Every vertex has cofinally many descendants. The whole graph is an inspecies and a maximal specieslike cluster.

In the second completion the new vertex starts two infinite chains. A vertex on either chain has infinitely many descendants and infinitely many non-descendants. Thus the whole graph fails the identical-ancestry property (IAP), although it is connected and convex in itself.

The result holds even for an empty initial history. It does not claim that the second completion has no specieslike subsets. It does not assert diploid reproduction, fixed parent-label coverage, empirical plausibility, or a reconstruction of an actual future. These are graph-theoretic witnesses to non-identifiability from finite history. The core uses natural birthdates; transport to real dates is a separate interface.

## Relevance to Wong and Alexander

Wong et al. define finite interval-annotated genetic-history graphs. A finite node catalog cannot itself be Alexander's infinite population. The theorem identifies a stronger obstruction than cardinality alone: choosing an infinite continuation cannot be uniquely justified by the observed finite graph, even when old ancestry is preserved exactly and both continuations satisfy the population finiteness conditions.

An actual gARG needs a proved topological numbering before this theorem applies. `real/WongGARG.lean` supplies that numbering; the composition with it is documented in `WONG-FINITE-COMPLETION.md` when checked. This does not supply the biological owner mapping from genomes or cells to organisms, and should not be described as an unconditional genomic-to-species inference.

## Endpoints

- `old_reachability_exact`: old ancestry is unchanged in both completions.
- `join_biosphere`, `fork_biosphere`: natural-date eligibility.
- `join_inspecies`, `join_maximal_specieslike`: positive whole-population results.
- `fork_not_iap`: explicit negative result.
- `finite_history_does_not_determine_species`: complete existence statement, including root finiteness and connectivity.

These are deductions developed for this project. No priority or novelty claim is made without a separate literature review.
