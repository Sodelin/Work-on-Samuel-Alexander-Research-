# Alexander submission revision drafts

These are edits to existing queued entries. They have not been submitted. Original provenance, solve dates and entry identities are retained unless a field below explicitly replaces them. Titles and limited fields pass UTF-16 character counts.

## universal-avoider

### submit-name (84/200)

No countable universal family of avoiding populations, even with exact parent counts

### submit-statement (788/1200)

Can populations avoiding a fixed infinite label sequence be represented inside one universal population, or a countable family? Alexander poses the universality direction in Biologically Unavoidable Sequences (2013), Section 6, p. 12, by analogy with Cherlin and Shelah. Here an embedding is an injective map preserving adjacency after forgetting directions and labels. Populations are infinite genealogies with finitely many roots, finite children, real birthdates increasing along edges, finite birth sublevels, and a parent of every label at every nonroot. We ask whether universality is possible even within the subclass having exactly one incoming parent of each label. This is the ordinary subgraph-embedding interpretation of a source question that does not prescribe one category.

### submit-resultNote (947/1000)

No countable catalogue suffices. From any population avoiding s, the checked construction produces another avoider with the same roots and exactly one parent of each label at every nonroot that embeds into none of any prescribed countable family of population hosts. It defeats every injective map with any finite global bound on edge stretch. Parent selection preserves avoidance; terminal cloning preserves the selected infinite-word language exactly. If the original population already has the required parent counts, selection is unnecessary and its entire language is retained. The essential population-specific step preserves chronology, finite pasts, roots and exact incoming-parent sets while creating enough vertices to defeat finite host balls. The graph-growth obstruction is classical. The result permits terminal individuals and unbounded finite child counts; it does not settle fixed child caps or arbitrarily unbounded edge stretch.

### submit-verificationNote (870/1500)

Lean 4.33.1 with Mathlib pinned to 0df444a360eaa60ab8c11dca51a86af692955474. TerminalCloneAvoiders.lean contains 16 selected endpoints for the population construction, exact parent counts, root correspondence, language preservation/inclusion, and obstruction. The earlier GenericUniversalAvoiders.lean has 10 selected endpoints. All were covered by successful hosted Verify run 36631876391 at commit 1592b89731d10fc49019ff22cf2f93c7bc799118. This audit read the strongest endpoint hypotheses and checked that the relevant sources are unchanged at main ea70e6c; it did not rerun the compiler. Reported proof dependencies use only propext, Classical.choice and Quot.sound. Endpoint counts measure verification coverage. Internal agent reviews do not establish independent human verification or worldwide priority. Requested label remains Lean-checked, statement unaudited.

### submit-submitterNote (812/1000)

The contribution is a negative answer to the explicit ordinary-embedding interpretation of Alexander's question, strengthened to exact incoming-parent counts. Cherlin-Shelah supplies the embedding convention. Lehner (2023), citing de Bruijn through Rado, supplies the classical local-finiteness context. Nonuniversality for all locally finite graphs alone does not prove it for this restricted population subclass; the preservation construction supplies that step. Present the countable-family and finite-stretch conclusions as proved refinements, not as newly invented diagonalization. Parent selection may shrink the original language, so exact language equality is claimed only for cloning itself or when selection is unnecessary. No claim of resolving every embedding category or historical priority is made.

### Additional or replacement sources

- [Original question: published Section 6, page 12](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v20i1p31/pdf/)
- [Classical host criteria and de Bruijn attribution](https://arxiv.org/pdf/2205.12824)
- [Weak versus strong universality: Introduction](https://arxiv.org/pdf/math/0512218)

## ordinal-realization

### submit-name (72/200)

Exact ordinal certificates and pruning characterize sequence realization

### submit-statement (754/1200)

Which infinite labelled populations realize a specified sequence? Alexander (2013), Section 6, p. 12, asks for such a characterization and singles out ordinal numbers, by analogy with Schmidt's rayless-graph rank. We give an exact characterization on reachable vertex/phase states: (v,k) is included precisely when a finite path spelling the first k letters can end at v. A transition follows an edge labelled by the next required letter. The ordinal criterion works for arbitrary vertex and label types without finite branching. When each state has finitely many matching successors, an additional question is exactly which states survive repeated deletion of states with no surviving child, and what measures the continuation length of a deleted state.

### submit-resultNote (961/1000)

Avoidance is equivalent to a strictly decreasing ordinal certificate on reachable states. With finite per-label branching, natural certificates suffice. Repeated pruning has a greatest fixed-point core: a starting state survives every finite round exactly when an actual infinite path spells the whole sequence from that vertex. Outside the core, even in a population that also has realizers, each state has an attained maximum continuation length h, the least natural decreasing certificate; it survives round n exactly when n <= h and is removed at h+1. Complete finite-fibre blow-ups preserve every corresponding least matching height. Thus those heights, after forgetting multiplicity and adjacency, do not determine the embedding obstruction. The rank and compactness methods are classical; this is a precise source-specific characterization and invariant analysis, with no arbitrary-infinite-input decision algorithm or new Schmidt-rank hierarchy claimed.

### submit-verificationNote (967/1500)

The generic certificate chain has 8 natural-certificate and 3 ordinal-certificate selected endpoints. The September 29 extension adds 10 pruning, 9 mortal-rank and 7 rank-transport selected endpoints. The decisive endpoints include avoids_iff_ordinal_certificate, realizes_iff_surviving_start, matching_state_dichotomy, survives_iff_le_height and avoider_has_exact_rank_transport. Successful hosted Verify run 36631876391 checked the sources at commit 1592b89731d10fc49019ff22cf2f93c7bc799118; the audited files are unchanged at main ea70e6c. Lean 4.33.1 and pinned Mathlib 0df444a360eaa60ab8c11dca51a86af692955474 were used. Standard reported axioms only. This publication audit checked statement correspondence and prior-art context without recompiling. The generic ordinal theorem directly applies Mathlib's well-founded rank. Schmidt rank is a distinct invariant and is not formalized by these endpoints. Requested label remains Lean-checked, statement unaudited.

### submit-submitterNote (788/1000)

The source asks for a characterization, not specifically a new transfinite hierarchy. This result gives exact membership, pruning, least finite heights, and a checked limitation of those heights as structural invariants. The underlying rank characterization and finite-branching compactness are established mathematics; the submission should be assessed as an application to Alexander's explicit question with formal refinements. The artificial root of the separate history tree has infinite branching and cannot be inserted into the finite-branching state theorem. Its ordinal rank omega and written Schmidt rank 1 do not distinguish avoiders. We retain partial scope for the broader analogy and do not advertise a new general termination theorem or classification up to graph embedding.

### Additional or replacement sources

- [Original ordinal-characterization direction, Section 6 p.12](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v20i1p31/pdf/)
- [Classical rank construction actually used](https://leanprover-community.github.io/mathlib4_docs/Mathlib/SetTheory/Ordinal/Rank.html)
- [Schmidt separator rank: Definition 2, page 3](https://arxiv.org/pdf/0911.3803)
- [Earlier termination and fixed-point framework](https://www.di.ens.fr/~cousot/publications.www/CousotCousot-POPL12-ACM-p245-258-2012.pdf)

## founder-window

### submit-name (85/200)

Maximal specieslike clusters without a common ancestor, using a fixed founding window

### submit-statement (867/1200)

Can every organism inhabit a maximal specieslike cluster under constraints that do not require a common ancestor? Alexander's Specieslike clusters based on identical ancestor points (2026), Section 6, proves an existence theorem using common ancestry and reflection, then explicitly asks for alternatives without common ancestry. For each fixed real Delta >= 0, we replace common ancestry by a founding-window condition: all internal founders of a cluster are born within Delta of its earliest member. A founder has no strict ancestor inside the cluster; it need not be parentless in the ambient graph. We retain connectedness, ancestry convexity, the identical ancestor point property (IAP), and reflection. The ambient graph has natural-number identifiers, real chronological birthdates with finite strict earlier sublevels, and finitely many children per organism.

### submit-resultNote (831/1000)

Every organism belongs to an inclusion-maximal cluster with IAP, convexity, connectedness, reflection and the prescribed real founding window. More strongly, every cluster satisfying those requirements extends to a maximal one. The same Delta applies to every competitor. The proof supplies a genuine seed through each organism, proves preservation under directed unions, and transports maximality back to the original real birthdates, including ties. A written two-founder merging-ray example satisfies the zero-duration window and all retained conditions but has no common ancestor, so the replacement strictly enlarges the admissible class. This answers the mathematical non-CA direction. Maximality is within the fixed-window class; uniqueness, a species partition and biological plausibility of the window are not established.

### submit-verificationNote (974/1500)

The eight founder-window modules contribute 50 selected endpoints to the 151-endpoint real/Mathlib audit. The strongest public endpoint is RealSpeciesTheorem.every_vertex_in_maximal_real_window; maximal_window_extension proves extension of every existing admissible cluster. The seed, directed-union IAP, real-window closure, constrained Zorn argument and faithful reindexing are checked. Successful hosted Verify run 36631876391 covers commit 1592b89731d10fc49019ff22cf2f93c7bc799118, and these real sources are unchanged at main ea70e6c. Lean 4.33.1, Mathlib 0df444a360eaa60ab8c11dca51a86af692955474, with only standard reported axioms. The two-founder example establishing strict weakening is a written argument in REAL-FOUNDER-WINDOW-THEOREM.md, not one of these Lean endpoints. This audit inspected source correspondence without recompiling. Requested label remains Lean-checked, statement unaudited; no independent human expert review or worldwide priority is claimed.

### submit-submitterNote (793/1000)

The exact target is the paragraph after Theorem 13 in arXiv:2602.05274v1, Section 6, p.17. Informal Question 4 on p.9 also requests biological plausibility, which this mathematical theorem does not certify. The article is published in Journal of Mathematical Biology 92, article 41 (28 February 2026), DOI 10.1007/s00285-026-02361-x; the publisher full text was gated, so the exact wording was checked in the accepted arXiv manuscript. Our result changes the admissible maximality class. It does not claim that every organism lies in an unrestricted maximal specieslike cluster. Its strongest presentation is that common ancestry can be replaced by a literal real-time bound on internal founders while retaining universal per-organism existence. Keep the original 25 September 2026 solve date.

### Additional or replacement sources

- [Exact source request after Theorem13, accepted manuscript p.17](https://arxiv.org/pdf/2602.05274v1#page=17)
- [Published article identity and version](https://doi.org/10.1007/s00285-026-02361-x)
- [Checked real-window theorem and written strictness witness](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/1592b89731d10fc49019ff22cf2f93c7bc799118/notes/REAL-FOUNDER-WINDOW-THEOREM.md)
