# Additional source checks for the ancestry and finite-edit contributions

Review date: 25 September 2026 UTC. This supplements the repository's earlier
query log. It records a bounded extension of that review, not an exhaustive
negative literature search.

## Exact root-lane queries

One `web.run` batch used these four strings without date or domain filters:

- `"biologically unavoidable" "three"`
- `"biologically unavoidable" "finite" "changes"`
- `"biologically unavoidable" "fixed" "gender"`
- `"Thue-Morse" "8/3" path`

The results were mostly Alexander's original papers and irrelevant uses of
the words. An extremal overlap-free-word paper also used $`\frac{8}{3}`$, but a shared
constant does not identify a matching path-length theorem. This batch supplies
no reliable negative finding about the proposed cap or finite-edit result.

A second batch used:

- `"Universal graphs with a forbidden subtree" Cherlin Shelah`
- `"The Structure of Rayless Graphs" Halin rank`

These located author-hosted primary materials and publication records.
The explicit comparison is in `OLDER-CONSTRUCTIONS-AND-RANK-AUDIT.md`.

## alphaXiv primary-text retrieval

The `answer_pdf_queries` tool was called on `1212.0186v2` with these exact
questions:

1. “In Sections 3 and 4, what exact construction of an avoiding population is
   given, and what maximum number of children per vertex does it imply? Include
   relevant definitions and proofs with vertex genders or edge genders.”
2. “Do the avoidance examples or remarks cover every non-eventually-periodic
   binary sequence, or only specific families? Are their vertex descendant sets
   cofinite, or do they form an inspecies?”
3. “Does the paper contain a finite-prefix modification or backward-extension
   lemma that transports finite matching paths between two different
   target-dependent avoiding graphs?”

The response supplied raw page text for all nine PDF pages. Definitions 6 and
8, Theorem 6, Propositions 11 and 16, Corollaries 12 and 17, and Section 6 were
inspected. The child counts and cofinite-descendant proofs in our accompanying
note are deductions from the displayed definitions, not statements that the
retrieval tool found quoted in the paper. The tool's returned text was treated
as source material, not as a mathematical verdict.

## Direct theorem comparisons

| Primary source | Passages inspected | Consequence for this contribution |
|---|---|---|
| [Wong et al., published 2024 PDF](https://www.pure.ed.ac.uk/ws/portalfiles/portal/458588307/iyae100.pdf) | Version-of-record cover; Genome ARGs, journal pp. 2–3, Figure 1 and its description | The genome-to-pedigree relationship already appears in the source. Our adapter is conditional and omits full gARG invariants. |
| [Cornell, Universal Mapping Properties](https://pi.math.cornell.edu/~kassabov/math4330.fall19/cornell-only/Universal.pdf) | Theorem 1 | Recovery by a decoder is an instance of quotient factorization. This is a teaching source for an established theorem, not an originality claim. |
| [Horstmeyer and Atay](https://arxiv.org/html/1607.01237#S2.SS2) | Section 2.2, definition and propositions on exact lumpability | A smooth continuous-time analogue of projected dynamics; not the same model as our discrete interface. |
| [Cherlin–Shelah author preprint](https://shelah.logic.at/files/182588/850.pdf) | Introduction, Theorem 1, scope of finite forbidden graphs | No checked reduction from the finite undirected exclusion theorem to the prescribed infinite labelled-path avoidance problem. |
| [Bonato et al., Twins of rayless graphs](https://www.uni-ulm.de/fileadmin/website_uni_ulm/mawi.inst.081/Henning/raylesstwins.pdf) | Definition 2 and discussion of Schmidt rank | This graph rank differs from ordinary well-founded tree height. The original Halin full text was not obtained. |
| [Alexander, inspecies paper](https://arxiv.org/html/1201.2869) | Definition 4 and Propositions 5–6 | Supplies the established minimality/cofinite-future framework; it does not assert the new uniform cap-three construction. |

The independent observation review also checked Hermann–Krener and
Shalizi–Crutchfield for the distinction between current observations, histories,
and predictive representations. Kemeny–Snell Theorem 6.3.2 was available as
indexed original text, but a direct PDF request timed out. These access limits
are preserved in the ancestry/observation note.

The independent ten-proposal reviewer used twelve further queries in three
batches and inspected the cited automata, regular-sequence, cycle-mean and
cellular-automaton sources. Only query categories, not every exact string,
were retained in that review. Its accompanying packet therefore does not
present that search as a reproducible exhaustive exclusion.

## Source pin

`git ls-remote` identified classification-repository main at
`3d6175e3e23f67bd68e7be591b5a9a6d04e496a3`. Its
[pinned manuscript](https://raw.githubusercontent.com/avg-netizen/biological-unavoidability/3d6175e3e23f67bd68e7be591b5a9a6d04e496a3/paper.md)
was then opened and checked for Sections 2–4. The explicit binary construction,
four-child binary vertex lift, Thue–Morse row identities and backward-prefix
method match the equations used in the new written packet. This source pin is
separate from the local formalization's commit and verification receipts.

## What this search changed

- Whole-inspecies avoidance already occurs in Alexander's older constructions.
  The candidate improvement must specify prescribed-target scope and child cap.
- Alexander already cited the universal-graph and ordinal-rank directions.
  They should not be presented as connections he had overlooked.
- The observation interface has direct quotient and lumpability precedents.
- Finite-edit transport and cap-three attainment now have explicit written
  arguments, with their new Lean status left to the owning implementation.

No inspected source was verified to state the exact finite-edit sharp
coefficient or the particular cap-three productive-core result. Equivalent
encodings, unindexed work, and unpublished ideas remain outside that finding.
