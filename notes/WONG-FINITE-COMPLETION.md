# Finite Wong gARGs and opposite infinite Alexander completions

## Result and scope

[WongAlexander.lean](../real/WongAlexander.lean) connects the repository's actual finite interval genome-ARG model to the Alexander graph definitions. The substantive completion theorem starts with a finite gARG and derives the ordering and embedding needed for two infinite extensions. It does not assume that the finite input is already an Alexander population.

For every represented finite gARG G, the theorem constructs an injective node map into each of two infinite populations A and B. Both preserve exactly every original raw topology edge and every original ancestry path between copied nodes. Both have increasing real birthdates, finitely many vertices born before any real date, finitely many children at each vertex, finitely many roots, and a connected underlying undirected graph. Nevertheless:

- The whole population A is an inspecies and a maximal specieslike set.
- The whole population B fails the infinite ancestry property, IAP, and therefore cannot be specieslike as a whole.

This is an abstract graph-completion ambiguity theorem. The injective map copies genome graph nodes into abstract population vertices. It is not an inferred genome-to-organism ownership map. No biological future, reproductive pedigree, recombination process, gender labelling, or interval inheritance on newly added edges is claimed.

Checked with the pinned Lean toolchain by the root task: standalone WongAlexander compilation exited successfully, and all eight printed endpoints used only permitted standard axioms or no axioms. The checked source SHA-256 is 1EC04C06714F359D791CDE0B4892443404F887C486BB59E35F4F24A35C1CB666. This check is separate from the final aggregate repository audit. The core completion theorem and finite gARG foundation were also checked separately before composition.

## The actual finite model

The input is WongGARG.GARG Node Coord, from [WongGARG.lean](../real/WongGARG.lean). It supplies a finite node catalog, designated samples, finitely represented disjoint half-open inheritance intervals, and an acyclic raw topology.

This model is motivated by Wong et al. (2024), [*A general and efficient representation of ancestral recombination graphs*](https://doi.org/10.1093/genetics/iyae100), especially its genome-ARG definition and Appendix E. The paper's nodes represent genomes; their identifiers do not themselves determine birth order.

The foundation derives an injective natural-number code from the number of strict ancestors, with a finite-identifier tie breaker. Acyclicity makes that code strictly increase along edges. Every code is below the square of the node count. Thus the ordering supplied to the completion theorem is proved from the input graph, not asserted as an extra biological assumption.

The coding can leave unused identifiers inside its finite bound. Those identifiers are filler vertices in the extension, and exact path reflection proves that they create no new ancestry between the original copied nodes.

## Why the two completions work

The checked core [FiniteHistoryCompletion.lean](../lean/SamuelAlexanderResearch/FiniteHistoryCompletion.lean) retains the entire birth-ordered input prefix and connects each old vertex to a new common anchor.

For A, the future is a single infinite chain. Every vertex eventually reaches every sufficiently late vertex. Its strict descendants are cofinite, which yields whole-population inspecies and specieslike status.

For B, the future splits into two infinite chains. A vertex strictly inside one branch has infinitely many descendants in its branch and infinitely many non-descendants in the other. This refutes the IAP dichotomy even though the underlying undirected graph remains connected through the common anchor.

All newly added edges point forwards in time. Therefore no new path can leave the original history and return to it. Exact raw ancestry among copied gARG nodes follows from this prefix preservation and the foundation's injective path encoding.

The real birthdate map is explicit: a natural-number vertex v is assigned its real-valued cast. The Archimedean property supplies a finite natural bound above any real date, so a finite list covers every real birthdate sublevel. This closes the natural-date-versus-real-date difference for these particular completion witnesses.

## Actual sample-extraction preservation

The same module also connects the gARG sample definition to the generic [ancestral-material restriction](ANCESTRAL-RESTRICTION.md), rather than maintaining two disconnected versions of sample ancestry.

| Endpoint | Exact conclusion |
| --- | --- |
| sample_ancestral_iff | G.SampleAncestral is the generic sample-or-path-to-sample predicate for G.AtLocus. |
| extracted_edge_iff_restrict | The actual gARG extracted edge relation is exactly generic ancestral-material restriction. |
| extracted_sample_path_iff | For any fixed genomic location and any designated sample, extraction preserves exactly all original paths ending at that sample. |
| extracted_contracted_sample_path_iff | The actual extracted relation, after retained-node elimination, preserves exactly original fixed-location ancestry into any retained designated sample. |
| finite_catalog_not_infinite | A finite node catalog cannot itself satisfy the repository's infinite-vertex axiom. |
| natural_biosphere_has_real_dates | Every natural-date biosphere in this interface has an explicit real-date presentation with finite real sublevels. |
| old_encoded_path_iff | Strict paths in the bounded natural-number copy are exactly strict paths in the original gARG topology. |
| actual_garg_opposite_infinite_completions | The full opposite-completion result, with literal real dates, exact copied edges and paths, finite children and roots, and connectivity. |

Sample extraction here preserves original node identities and keeps unary ancestry. It is ancestral-material pruning, not all tskit simplification options. The separate sample-restriction counterexample shows why genomic location labels must not be erased prematurely.

## What can and cannot be inferred

The new theorem establishes a concrete limitation on inferring global infinitary specieshood from a finite genome-history graph: even complete agreement on that graph's raw topology and all its ancestry paths leaves the whole-population IAP verdict undetermined.

It does not say that biological information is useless, that actual species cannot be identified by other criteria, or that no specieslike subset exists in B. Additional biological constraints could exclude one or both constructed completions. Such constraints must be stated and checked; they do not follow from the finite DAG alone.

There is also a type-level obstruction: the finite gARG's node catalog cannot itself be the infinite ambient population required by the Alexander interface. One must supply an infinite extension or another justified interpretation. A genome-owner map remains a separate biological correspondence, governed by the explicit compatibility hypotheses of the repository's existing HistoryProjection theorems.

Nothing in these results proves graph self-similarity. The foundation's invariance of local edges and ancestry between genomic breakpoints is piecewise constancy in the genome coordinate, which is a different mathematical property.

These are verified targets for a substantial finite-data and infinite-population bridge. They are not a formalization of the entirety of Wong et al.'s paper, its inference algorithms, stochastic models, or scientific applications.