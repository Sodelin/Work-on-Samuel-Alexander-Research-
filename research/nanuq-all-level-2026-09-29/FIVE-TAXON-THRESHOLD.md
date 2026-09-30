# Five total taxa are the sharp test cutoff for the parameter family

**Theorem.** For the four-score family `(c,s,a,o)`, with the exceptional shared-anchor entry fixed at 1, universal nonnegativity of every circular anchor coefficient on adjacent-copy plane trees of arbitrary finite size is equivalent to checking every such coefficient on representations with **at most five total distinct taxa**. Five is the least sufficient cutoff for this parameter-family criterion: four total taxa do not suffice.

This sharpens the size of the necessary *parameter test collection*. The structural restriction argument still retains at most six labels. No claim that every individual configuration can be restricted to five labels while preserving its coefficient is required or made.

## Definitions and exact equivalence

Let `P_n(theta)` mean that all circular anchor coefficients are nonnegative for every adjacent-copy plane tree on `n` distinct taxon labels, at the score vector `theta=(c,s,a,o)`. Every label occurs once or twice, its two copies are adjacent in the cyclic tip order, and the quartet system is the union over complete one-copy-per-label selections.

For distinct anchors `p,q`, the symmetric matrix has diagonal zero. An off-diagonal queried pair equal to the anchors has entry 0, a pair sharing exactly one anchor has entry 1, and a disjoint pair has entry `2c`, `2s`, `2a`, or `2o` according to its singleton cherry, singleton separated, two-topology adjacent, or two-topology opposite quartet class. A coefficient at two distinct circular gaps `(u,u+)` and `(v,v+)` is

`M(u,v) + M(u+,v+) - M(u,v+) - M(u+,v)`.

Write `P_<=m(theta)` for the conjunction of `P_n(theta)` over `3<=n<=m`, and `P_all(theta)` for the conjunction over all finite `n>=3`. Then, for every real score vector, the following are equivalent:

1. `P_all(theta)`.
2. `P_<=5(theta)`.
3. `s=o=1`, `1/2<=a<=1`, and `0<=c<=a`.

The nonnegative-score convention can be imposed without changing this equivalence; the displayed constraints already imply it.

## Why five suffice

First, [ALL-LEVEL-PROOF.md, Section 3](ALL-LEVEL-PROOF.md#3-six-taxa-suffice-independent-of-k) proves a score-independent six-label restriction. A single anchor coefficient uses its four boundary labels and two anchors, with overlaps allowed. Retaining every copy of these labels preserves their displayed quartet sets and the four entries in the coefficient. It also preserves the two boundary adjacencies. Therefore

`P_all(theta) <=> P_<=6(theta)`.

Second, the saved exact enumeration and independent symbolic verification show that the normalized nonzero row sets for sizes at most five and sizes at most six are equal. Here a row is the integer coefficient vector of the affine form in `(1,c,s,a,o)`, divided by its **positive** greatest common divisor. This division preserves its sign. Identically zero coefficients impose no condition.

| Size | Independently saved quartet systems | Coefficients evaluated | Distinct nonzero normalized rows at that size |
|---:|---:|---:|---:|
| 3 | 1 | 9 | 1 |
| 4 | 3 | 108 | 10 |
| 5 | 16 | 1,600 | 16 |
| 6 | 102 | 22,950 | 16 |

The independent receipt does more than compare the two counts of 16: its complete union has exactly 16 rows, and every one has a recorded witness with at most five labels. Thus no six-label row is missing from the collection at most five. Consequently

`P_<=6(theta) <=> P_<=5(theta)`.

Indeed, each nonzero six-label coefficient is a positive multiple of a normalized row already represented by a coefficient on at most five labels. The earlier representative may come from a different tree and different anchors. This is a statement about the shared parameter inequalities, not a five-label structural restriction of the original tree.

Finally, [PARAMETER-DOMAIN-AUDIT.md](PARAMETER-DOMAIN-AUDIT.md) proves that the common 16-row system is equivalent to `s=o=1`, `1/2<=a<=1`, `0<=c<=a`. Combining these three equivalences proves the theorem's sufficiency and exact parameter characterization.

In certificate terms, the test collection at most five contains 20 quartet systems and 1,717 anchor coefficients, arising from the previously enumerated 5,832 tree/duplication configurations. The earlier six-label computation supplies the proof that the additional 102 systems impose no new parameter inequality; this note does not discard that evidence or pretend it was unnecessary to establish the cutoff.

## Why four do not suffice: an actual five-taxon representation

The ten rows occurring on at most four labels are exactly equivalent to

`s=o=1`, `0<=a<=1`, `0<=c<=1`.

This larger box contains the nonnegative score vector

`theta_* = (1,1,1/2,1)`.

The saved focused receipt verifies that all 9 coefficients on the three-label system and all 108 coefficients on the three four-label systems are nonnegative at this point. Thus `P_<=4(theta_*)` holds.

An actual five-label counterexample is recorded in the owner's [FOUR-TAXON-OBSTRUCTION.md](C:/Users/Owner/Documents/Alexander-Open-Questions-2026-09-29/field-priorities/nanuq/formal-full/FOUR-TAXON-OBSTRUCTION.md) and [exact receipt](C:/Users/Owner/Documents/Alexander-Open-Questions-2026-09-29/field-priorities/nanuq/formal-full/FOUR-TAXON-OBSTRUCTION.json):

- Distinct labels: `0,1,2,3,4`; expanded tip labels: `[0,0,1,2,3,4]`.
- Position-labelled plane tree: `[0, [[[1,2],3], [4,5]]]`, with physical tip 0 attached above the displayed subtree.
- Duplication mask: `1`; packed quartet pattern: `4717`.
- Quartet codes in lexicographic order: `[5,5,1,1,1]`.
- Anchors: `(0,1)`; gap indices: `(2,4)`, whose successors are `(3,0)`.

The existing focused witness check built the graph, independently read its quartets by distances, and checked both global choices of the duplicated label. Its four relevant entries are

`M(2,4)=2a`, `M(3,0)=1`, `M(2,0)=1`, `M(3,4)=2c`.

Hence the actual unhalved coefficient is

`alpha = 2a + 1 - 1 - 2c = 2(a-c) = -1` at `theta_*`.

This is an attained coefficient on the representation, not merely a violated abstract inequality. It shows `not P_5(theta_*)` while `P_<=4(theta_*)` holds. Therefore any cutoff at most four fails, whereas five succeeds by the preceding proof. Five is the sharp cutoff across the four-parameter family.

## Evidence and formal-status boundaries

- **Score-independent six-label restriction:** [ALL-LEVEL-PROOF.md, Section 3](ALL-LEVEL-PROOF.md#3-six-taxa-suffice-independent-of-k). Section 6 records its use for the full parameter family.
- **Complete rows and actual small witnesses:** [independent-parameter-domain-check.json](independent-parameter-domain-check.json), keys `rows_by_size`, `nonzero_normalized_rows`, `inequalities[*].row`, and `inequalities[*].witness.taxa`. Its 16 witnesses all have at most five labels. [parameter-domain.json](parameter-domain.json) provides the separately generated packed-pattern witnesses.
- **Independent row extraction and exact domain proof:** [PARAMETER-DOMAIN-AUDIT.md](PARAMETER-DOMAIN-AUDIT.md), including the exact checker and nonnegative-generator certificates.
- **Actual four-cutoff failure:** the owner's `FOUR-TAXON-OBSTRUCTION.md` and `.json`, especially `four_taxon_certificate_passes`, `rooted_plane_tree`, `independent_quartet_codes`, `terms`, and `coefficient`.
- **Existing Lean algebra statements:** [AllLevelParameterDomain.lean](C:/Users/Owner/Documents/Alexander-Open-Questions-2026-09-29/field-priorities/nanuq/formal-full/AllLevelParameterDomain.lean), definitions `AllRows`, `FourTaxonRows`, `ExactDomain`, and theorems `all_rows_iff_exact_domain` (line 32), `four_taxon_rows_iff_box` (line 42), and `four_taxon_certificate_insufficient` (line 53). Its [saved log](C:/Users/Owner/Documents/Alexander-Open-Questions-2026-09-29/field-priorities/nanuq/formal-full/AllLevelParameterDomain.log) records the ordinary Lean axioms `propext`, `Classical.choice`, and `Quot.sound`. The source expressly separates this algebra from the external representation and enumeration proof.

This note is a deduction from the existing computer-assisted certificate and the actual focused obstruction. No tree family was re-enumerated, no prior checker was rerun, and no Lean build was performed. The unbounded five-cutoff theorem is not being claimed as a newly completed end-to-end Lean formalization.

The cutoff counts **total distinct taxon labels**, including duplicated labels. The obstruction has five taxa, four of them single-copy, and six physical tips. It therefore does not refute a differently defined bound counting only ordinary single-copy leaves.

The minimality statement concerns universal **parameterized anchor positivity**. It is not a minimal bound for the original fixed NANUQ score `(0,1,1/2,1)`, and it is not a necessity theorem for circularity of the aggregate unweighted source-network distance. Negative individual anchors may be offset after aggregation. No broader priority claim is inferred from the cutoff result.
