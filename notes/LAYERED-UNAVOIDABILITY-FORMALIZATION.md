# Strict layering realizes every binary word

`LayeredUnavoidability.every_word_realized` checks the binary specialization
of the layering comparison in `SPECIESLIKE-GENERALIZATION.md`. Its inputs are
an actual `BinaryNatPopulation`, a natural-number layer function, edges that
advance exactly one layer, every root in layer zero, and a vertex at every
layer depth. Its target word is arbitrary, with no periodicity condition.

Backward parent choices build a correctly ordered finite matching path from
layer zero to any vertex in layer `n`. Layer-zero vertices are roots, so all
these paths start in one finite set. Their endpoints cannot remain bounded
in birth order because a path of `n` strict edges ends at index at least `n`.
The internally proved finite-branching argument then constructs an infinite
matching path.

The root-layer hypothesis excludes new roots in later generations. Requiring
incoming labels only at nonroots while allowing such later roots would not
justify the backward path argument. Likewise, skip edges do not satisfy
strict layering. Connectedness, one undirected end, and common future alone
are insufficient replacements.

This formalizes a direct comparison of Alexander's [2026 Example
14(1)](https://arxiv.org/html/2602.05274v1#S6) with the [2026 classification
construction](https://github.com/avg-netizen/biological-unavoidability/blob/main/paper.md).
The finite-branching method is classical. This file treats Boolean labels;
the broader arbitrary-alphabet prose statement is not silently claimed as
an endpoint of this specialization.

Reproduction: `lake build SamuelAlexanderResearch.LayeredUnavoidability`,
followed by the integrated endpoint audit.
