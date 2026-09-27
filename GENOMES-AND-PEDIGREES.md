# The same genome history can hide different organism ancestry

**A reading route for the discovery track.** We constructed a precise example
in which every recorded genome transmission is the same, but two ways of
grouping genome copies into individuals give different answers to an
organism-ancestry question. The complete proof and source comparison are in
the [research note](research/genome-pedigree/README.md).

The question connects two papers. [Wong and colleagues](https://doi.org/10.1093/genetics/iyae100)
represent genetic inheritance using genomes and the intervals transmitted
between them. [Alexander](https://arxiv.org/html/2602.05274v1) studies ancestry
between organisms, including an idealized infinite future. His identical
ancestor point condition, **IAP**, says that every member of a candidate group
has either finitely many descendants or finitely many non-descendants within
that group. Are genome transmissions enough to determine that condition?

**Our answer is no when individual ownership is omitted, even with unusually
strong information about actual transmissions.** This is a statement about a
specified mathematical observation, not about every kind of genetic data.

| What the two histories share | What can differ |
|---|---|
| Every genome-copy identity, transmission, generation and interval | Which two contemporaneous copies belong to one organism |
| Four diploid organisms per generation | Whether every organism eventually becomes an ancestor of everyone later |
| Two distinct parents per nonfounder; two children per organism; connected pedigrees | Whether the whole population satisfies IAP |
| Ownership through any prescribed finite generation | The unobserved ownership assignments after that generation |

The construction has eight persistent genome-copy lines. In one grouping,
organism ancestry spreads across the population: after three generations each
organism is an ancestor of all later organisms. In the other, the later
pedigree stays divided into two reproductive groups. An organism in one group
has infinitely many descendants there and infinitely many non-descendants in
the other. The full pedigree remains connected through its earlier history.

This also exposes a specific failure in a proposed bridge. An organism can
inherit one copy from its parent and transmit its other copy to its child.
Each parent–child link is witnessed by a genome transmission, yet those two
witnesses do not join into a genome ancestry path. **Preserving every edge
does not by itself preserve organism ancestry paths.**

The verification uses the repository's existing definitions. It covers the
all-generation counterexample, exact two-copy ownership, the parent and child
counts, connectivity, the arbitrary-prefix impossibility result, and the path
obstruction. Every finite truncation is also mapped into the existing Wong
gARG structure; the organism graphs meet Alexander's real birthdate
conditions. The [receipt and replay instructions](research/genome-pedigree/README.md#verification)
identify what was checked.

The practical lesson is to preserve ownership metadata when an analysis needs
organism ancestry. It is already supported by tools such as
[tskit's individual associations](https://tskit.dev/tskit/docs/stable/data-model.html).
For this particular pair of histories, checking whether two specified copies
belong to the same organism can distinguish them. That observation is extra
information, not something recovered from the common transmission graph.

**What is new remains a bounded claim.** Pedigree ambiguity and the difference
between genetic and genealogical ancestry are established mathematics. Our
[prior-work review](research/genome-pedigree/PAIRING-PRIOR-ART.md) found no exact
version of this constrained construction with opposite IAP outcomes. That
makes it a candidate contribution; it does not establish worldwide priority.

This is a proved mathematical example. It is neither a fitted prediction nor
an experimentally supported biological mechanism. We have not proved that
the two histories have the same statistical likelihood, that such an infinite
history has positive probability, or that biological species obey IAP. The
earlier [Royal Society time-and-memory track](TIME-AND-MEMORY.md) remains
separate, and none of its authors' full open questions is declared solved here.

The next research decision is whether a biologically motivated restriction on
ownership, or an explicit stochastic observation model, preserves this
ambiguity. A broader claim needs that additional theorem and a further
novelty review.
