# Diamond contraction and a common finite interval output

This isolated draft develops the information-loss example suggested by
Wong et al. (2024), **Appendix G, journal pp. 16–17**, and **Appendix H,
p. 17**. It uses the checked finite interval-gARG and retained-node
contraction definitions. It extends the previously published packet with its own current source receipt.

Source: [published paper](https://www.pure.ed.ac.uk/ws/portalfiles/portal/458588307/iyae100.pdf),
[DOI](https://doi.org/10.1093/genetics/iyae100).

**Individual verification status:** the coordinator's latest serialized Lean
compilation exited 0 and checked all 13 printed endpoints, including the two common-output endpoints. Their reported
axioms were confined to propext, Classical.choice and Quot.sound; no
sorryAx or additional assumption was reported. One unnecessary-simpa style
warning at source line 222 does not affect verification. The coordinator
and the independent foundation reviewer also passed the bounded
mathematical and source-scope review.

Checked source: [WongDiamond.lean](WongDiamond.lean).
SHA-256: A699E46D3A7790FB64AD93F3478DB2BD7A557CBCD2127185AF7177C21CB91163.

**Integration status:** the promoted module passed the fresh 101-endpoint mathlib aggregate audit. Hosted validation is a separate publication gate. The historical individual receipt below is not by itself a
new published packet or a complete formalization of Wong et al.

## Actual input graphs

Both graphs have the same four genome nodes, 0, 1, 2 and 3; node 3 is the
only sample. For a strictly interior cutoff in the common span [0,3):

- Edges 0→1 and 1→3 carry the left interval [0,cut).
- Edges 0→2 and 2→3 carry the right interval [cut,3).

The two examples choose cutoff 1 and cutoff 2. Their raw unlabelled
topologies coincide, but their genomic annotations differ.

The Lean draft constructs actual WongGARG.GARG values and proves:

- Acyclicity, using strictly increasing finite node numbers.
- Nonempty, proper half-open interval annotations.
- Exactly one stored record per parent-child pair.
- Unique local parenthood at every genomic coordinate.
- Sample support for every annotated edge-position incidence.

The latter distinction matters: this loss of information does **not** rely
on deleting an edge that was irrelevant to the sample. Every represented
edge-position incidence lies on a fixed-position path to sample 3.

## Exact contraction and preserved observations

Keep only nodes 0 and 3. The contraction relation replaces paths whose
internal nodes are unretained by single retained-to-retained edges.
For either cutoff, the exact result is:

~~~math
\operatorname{Contract}(G_x,\{0,3\})(a,b)
\quad\Longleftrightarrow\quad
x<3\ \land\ a=0\ \land\ b=3.
~~~

Coordinates are natural numbers, so x < 3 is exactly membership in [0,3).
For positions left of the cutoff the witness passes through node 1; for
positions at or right of the cutoff it passes through node 2. At every
in-domain position the contracted relation therefore contains exactly the
edge 0→3.

The contraction relation has endpoints satisfying the retained-node predicate on the original Fin 4 carrier. The extension below represents it by a concrete finite interval gARG on that same carrier; unused nodes 1 and 2 remain isolated.

The generic contraction theorem gives exact reachability preservation
between retained endpoints. In particular, every retained node has exactly
the same fixed-position ancestry to sample 3 before and after contraction.
This does not preserve path length, internal genome identities or the
crossover cutoff.

At position 1, the cutoff-2 graph has the raw edge 1→3, while the cutoff-1
graph does not. Consequently the two raw histories differ despite having
identical contracted relations at **every** coordinate.

## Exact checked endpoint map

The following source lines refer to the checked SHA-256 above. Each row
is a separate printed-axiom endpoint; these original 11 and the two added endpoints below all passed the latest individual run.

| Fully qualified endpoint | Source line | Exact scope |
|---|---:|---|
| WongDiamond.garg | 68 | Constructs an actual finite acyclic interval gARG for any natural cutoff strictly between 0 and 3. |
| WongDiamond.nonempty_annotations | 106 | Every stored record contains an interval. The record construction already enforces proper intervals. |
| WongDiamond.canonical_records | 112 | Any two stored records with the same parent and child are identical. |
| WongDiamond.unique_parent | 119 | At every coordinate, each child has at most one local parent. It does not assert a parent for roots or outside the span. |
| WongDiamond.sample_supported | 133 | Every annotated edge-position incidence has a same-coordinate continuation to designated sample 3, allowing the child itself to be the sample. |
| WongDiamond.contracted_relation_iff | 167 | Contracting to retained nodes 0 and 3 gives exactly the edge 0→3 at natural coordinates below 3, independent of the interior cutoff. |
| WongDiamond.retained_ancestry_iff | 194 | Nonempty reachability between retained endpoints is equivalent before and after contraction. |
| WongDiamond.sample_ancestry_iff | 200 | The same reachability equivalence specializes to retained ancestors and designated sample 3. |
| WongDiamond.contracted_relations_agree | 209 | The cutoff-1 and cutoff-2 contracted relations agree at every coordinate and pair of endpoints. |
| WongDiamond.raw_relations_differ | 215 | At coordinate 1 the cutoff-2 graph has edge 1→3 and the cutoff-1 graph does not. |
| WongDiamond.diamond_cutoff_information_loss | 226 | Bundles common samples, both admissibility predicates, unique local parents, complete sample support, contracted relation equality and the raw inheritance discrepancy. |

Supporting declarations identify the representation choices:
records at line 37; DiamondTopology at line 46; topology_iff at line 49;
the full raw locus characterization locus_iff at line 77; Keep at
line 148; and the two actual values cutOne and cutTwo at lines 206–207.
The retained/sample ancestry theorems are separate checked endpoints:
the final bundled collision theorem does not redundantly restate them.

## Paper-to-proof coverage

| Source item | Formal contribution | Boundary |
|---|---|---|
| Main text pp. 2–4: finite genomes with coordinate-annotated inheritance | garg constructs a concrete finite interval gARG, with the optional storage and unique-parent properties proved explicitly. | This is one exact finite instance, not a proof of every biological modelling assertion. |
| Appendix G, pp. 16–17: remove intermediate nodes while retaining selected genealogical relationships | contracted_relation_iff computes the retained-node output; retained_ancestry_iff and sample_ancestry_iff prove its exact ancestry preservation. | The output is the defined mathematical contraction relation; no tskit implementation or serialized table equivalence is claimed. |
| Appendix H, p. 17: diamond removal can discard breakpoint information | contracted_relations_agree and raw_relations_differ witness two distinct original cutoffs with the same complete contracted observations. | This proves non-injectivity of this contraction observation, not a statistical impossibility result for every observation model. |
| Relation to the existing full-relation cutoff recovery theorem | The parents 1 and 2 and their incoming sample edges are discarded by Keep. | No contradiction with crossover_cut_identified: that theorem retains fixed ordered distinct parents and the complete original local relation. |

## Interpretation

This is a concrete formal instance of the paper's distinction between
preserving a chosen simpler genealogy and preserving the full recombination
history. It complements the earlier invisible-edge example: ancestral-material
restriction and retained-node contraction have different information-loss
mechanisms. This example retains full sample support before contraction,
so the collision cannot be explained by an unused or empty raw edge.

It does not formalize tskit's simplify algorithm, prove a stochastic
identifiability theorem from DNA observations, or construct a biological
organism-owner map. It is an attributed mathematical example, not a claim
that diamond information loss was newly discovered.


## Common concrete finite interval output extension

The appended `collapsedGARG` has the same Fin 4 catalogue and sample set `{3}`, with exactly one record: parent 0, child 3, region `[0,3)`. Its DAG proof uses increasing node indices. `collapsed_represents_contraction` states that at every coordinate and endpoint pair this actual output has exactly the contraction relation of `garg cut`, for every natural cutoff satisfying `0 < cut < 3`.

`same_finite_output_hides_cutoff` bundles the same sample set for both inputs, the singleton record set, nonempty annotations, canonical records, local unique parenthood at every coordinate, full sample support, exact representation of both cutoff-1 and cutoff-2 contractions, and their original raw-edge discrepancy at coordinate 1. Thus there is one concrete valid finite interval output for the two different inputs, beyond equality of abstract relations.

This is an explicit common chosen representation, not a theorem that the automatic cell-grouping construction returns equal record objects. That construction does not coalesce adjacent intervals; it may retain the old cut as redundant syntax in `[0,cut)` and `[cut,3)`. The new full-span representation does not retain it. No globally minimal canonical segmentation or verified external serialization procedure is claimed.

**Extension verification:** the coordinator's serialized compilation passed all 13 printed endpoints for source SHA-256 A699E46D3A7790FB64AD93F3478DB2BD7A557CBCD2127185AF7177C21CB91163. All reported axioms were confined to `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or custom axiom appeared. The two added checked endpoints are `WongDiamond.collapsed_represents_contraction` and `WongDiamond.same_finite_output_hides_cutoff`. The complete promoted-source build and 101-endpoint aggregate audit also passed. Hosted validation remains tied to the subsequent publication commit.
The current integrated source inventory is in [the core receipt](../verification/formal-audit.json) and [the mathlib receipt](../verification/real-audit.json). All selected endpoints use only the permitted standard axioms.
