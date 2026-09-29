# Prior-work comparison for the recurrent-parenthood bridge

Audit date: 2026-09-25. This is a bounded search and statement comparison, not an exhaustive novelty determination.

## What is being claimed

The candidate theorem concerns an infinite, discrete-generation pedigree split into finitely many demes. Every deme is occupied at every generation. Each child has a same-deme parent. A fixed finite local window makes every organism an ancestor of its entire later same-deme cohort. After removing finitely many nonrecurring cross-deme links, eventual ancestry is exactly reachability in the recurring-link graph. Infinite subsets satisfy Alexander-IAP precisely when they lie in one recurring strongly connected component modulo a finite set.

The complete derivation is in [the manuscript](MANUSCRIPT.md). Its proof uses familiar finite-graph arguments. Mathematical correctness, faithful formalization, and originality are separate questions.

## Closest comparisons

**Alexander (2026).** [Specieslike clusters based on identical ancestor points](https://arxiv.org/html/2602.05274v1), Definitions 2–4, supplies the IAP, convexity and connectivity predicates. The paper explicitly separates genealogy from surviving genetic material and discusses one-way permanent splits. Our target is a sufficient-assumption classification in a restricted temporal pedigree, not a new definition of biological species or a replacement for its maximal-cluster theorem.

**Rohde, Olson and Chang (2004).** [Modelling the recent common ancestry of all living humans](https://doi.org/10.1038/nature02842), official [Supplementary Methods A](https://media.springernature.com/original/springer-static/esm/art:10.1038%2Fnature02842/MediaObjects/41586_2004_BFnature02842_MOESM1_ESM.pdf), pp. 1–3. Their two-parent random model uses a fixed connected undirected island graph, within-island uniform parent sampling and migration probability c/n. Theorem 2 gives an identical-ancestor time asymptotic proportional to graph diameter and log population size as population size grows. It permits lineage extinction. Our directed, deterministic, all-time subset classification has different assumptions and target. The underlying lesson that very rare reproduction between populations can connect genealogies is already established. We cannot claim that lesson as new. Reading coverage: model and theorem statements plus explanatory passages pp. 1–5; the complete technical proof was not audited.

**Casteigts, Flocchini, Quattrociocchi and Santoro.** [Time-Varying Graphs and Dynamic Networks](https://arnaudcasteigts.net/files/CFQS11.pdf), §§3.4 and 4, especially pp. 8–9. Time-respecting journeys and recurrence are established concepts. Their Class 6-to-Class 5 implication uses recurring edges and waiting to obtain recurring temporal connectivity. Our ancestry saturation enables the same waiting mechanism. The specific IAP subset classification is an application to investigate; the recurrent temporal-reachability idea is not original. Reading coverage: definitions and connectivity hierarchy, not every cited earlier temporal-network theorem.

**Conditional Borel–Cantelli.** The conversion from divergent conditional cross-parenthood probability sums to infinitely many realized events is a standard theorem. Its use allows history-dependent feedback without independent-event assumptions. It does not derive those probabilities from an epigenetic or cultural model.

## What remains unknown

No exact predecessor for the whole stated IAP/component equivalence was identified by this limited search. That observation does not establish novelty. A specialist may recognize it as a routine corollary of existing temporal-graph results. Independent review should compare the complete statement, especially its unusually strong no-lineage-extinction assumption, rather than a broad title.

A claim about actual culture-driven or epigenetically driven speciation additionally needs a defensible reproductive model and empirical evidence. None follows from this prior-work comparison.

## Reproducible search record

Search engine queries, 2026-09-25:

- "identical ancestors" "migration" graph
- "genealogical" "strongly connected" populations ancestors
- "identical ancestor" "deme" mixing
- "Samuel" "Alexander" "identical" "open" — broad-name false positives; narrowed to the exact paper.
- Rohde Olson Chang 2004 common ancestors supplementary graph migration identical ancestors theorem
- genealogical ancestry population structure recurrent migration strongly connected identical ancestor points theorem
- "Specieslike clusters" "recurrent"
- "identical ancestor point" "strongly connected"

The Yale-hosted PDF endpoint returned a retrieval error. The openly linked official Nature supplement was successfully read; no access-control workaround was used. Secondary semantic topic pages and social discussions were discovery results only, not evidence for a theorem or an absence claim.
