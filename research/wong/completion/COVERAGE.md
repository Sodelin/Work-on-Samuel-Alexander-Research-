# Wong et al. 2024: source coverage and checked completion progress

**The finite representation package has advanced; the whole paper is not yet formalized.** This ledger maps the substantive main text and Appendices A–I to checked results, exact remaining mathematical obligations and empirical reproduction. Abstract and Introduction summarize representation, the stochastic/data-structure distinction and software motivation already mapped in M01, M12–M13 and A03.

Source: Yan Wong, Anastasia Ignatieva, Jere Koskela, Gregor Gorjanc, Anthony W. Wohns and Jerome Kelleher, *A general and efficient representation of ancestral recombination graphs*, **Genetics** 228(1), iyae100 (2024). [Published PDF](https://www.pure.ed.ac.uk/ws/portalfiles/portal/458588307/iyae100.pdf), [primary full text](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/), [DOI](https://doi.org/10.1093/genetics/iyae100). The article is CC BY 4.0. The proof contracts are our interpretation; established results retain their attribution and no novelty is claimed.

## What is now checked

The [fresh aggregate Lean receipt](../../../verification/real-audit.json) at **2026-09-25 13:26:46 UTC** registers **209 Mathlib endpoints**, including **58 new endpoints in six modules**. Every promoted source hash was compared with both the integration manifest and this receipt, and all 58 names were found. Totals include other mathematics; they are not a percentage of this paper proved.

| Module | New endpoints | Exact checked addition | Claim rows |
|---|---:|---|---|
| [WongSampleTracing](../../../real/WongSampleTracing.lean) | 6 | Executable reference sample tracing, node-count fuel, exact sparse arrays and indexed reconstruction criterion. | E01–E02 |
| [WongRecordTracing](../../../real/WongRecordTracing.lean) | 5 | Actual interval-record scanning and end-to-end records-to-sample-array correctness. | E01–E03 |
| [WongEventDecoding](../../../real/WongEventDecoding.lean) | 17 | Normalized event conversion is injective with a classical range inverse; strict event kinds are recovered under explicit degree assumptions. | M04–M05 |
| [WongLocalSimplification](../../../real/WongLocalSimplification.lean) | 8 | Finite interval output for coordinate-dependent retention; samples-plus-branching instance and exact ancestry/parent/support guarantees. | F02, G04–G05 |
| [WongMemoizedTracing](../../../real/WongMemoizedTracing.lean) | 10 | Source-faithful visited-entry early stop, cache invariants, equality to reference extraction, actual-record composition and abstract write/check/lookup bounds. | M08, E01–E02 |
| [WongTimedHistory](../../../real/WongTimedHistory.lean) | 12 | Valid timed event histories with the same observed graph and retained dates but different recombination times and actual lineage counts; no exact time/count decoder. | B09, H02 |

**The qualification matters:** the event inverse is classical and range-restricted; interval lookup reads records rather than serializing output; local simplification remains noncomputable. Memoized cost results count abstract operations, and the timed witness has no stochastic likelihood model. Exact boundaries and all remaining obligations are below.

Module hashes, qualified endpoint mappings and historical receipts are in [coverage.json](coverage.json). The preceding 187-endpoint/four-module snapshot is retained there as history. All selected endpoints use only permitted standard axioms. Local aggregate verification does not assert that the hosted check for a later publication commit has passed.

## A short orientation

1. **Finite inheritance representation:** checked foundations include [WongGARG](../../../real/WongGARG.lean), local parents, ancestry and arity laws.
2. **Algorithms and inverse:** normalized mathematical decoding and actual-record memoized extraction now have checked proofs. Canonical finite interval serialization remains separate.
3. **Simplification:** coordinate-dependent finite output is checked. Above-MRCA interpretation, full normal-form/idempotence, adjacent coalescing and literal figures remain.
4. **Information loss:** a concrete timed graph now shows loss of hidden recombination time and intermediate lineage count despite equal retained dates. General likelihood and statistical conclusions remain unproved.
5. **Random processes and data:** probability laws, almost-sure absorption, asymptotic counts and reproduction of published software/data still require separate work.

### Exact memoized cost scope

Successful nonempty cache writes are at most the number of nodes. Cache checks and supplied-parent lookups are each at most writes plus the sample-list length. Repeated root lookups are counted because roots and unvisited entries both have `none`. These bounds do not assume constant-time record scanning, functional-cache access, updates or allocation. They are not CPU-time or tskit benchmarks.

### Exact timed-witness scope

Two actual seven-node histories place recombination at backward time 2 or 4. The specified contraction removes that event node and produces the same six-node interval graph with the same retained dates. At time 3, actual raw crossing-edge counts are 4 versus 3. This proves exact deterministic time/count nonrecoverability on the named family; it does not prove equal likelihoods, a stochastic law, a biological-species result or the reconstruction of arbitrary histories.

## Evidence and source review

The [core receipt](../../../verification/formal-audit.json) records 405 endpoints; historical Mathlib snapshots recorded 151 and 187. They remain identified in the JSON. This documentation lane reran no compiler.

The finite interval-gARG and older conditional [HistoryProjection](../../../lean/SamuelAlexanderResearch/HistoryProjection.lean) interface impose different requirements. The latter alone does not implement all paper definitions.

All main sections and Appendices A–I were inspected through primary PDF text and preserved primary XML, PMCID PMC11373519, with its hash recorded in the JSON. Requested PDF screenshots returned image-reference strings without visible images in this tool transport. **No visual PDF certification is claimed.** Primary MathML resolves the binomial rates; a visible B/E/F–G formula/figure check remains a bounded source-fidelity follow-up.

Pages below are printed journal pages. The PDF has an extra cover: journal 12 is viewer 13, zero-based screenshot index12.
## Three distinctions that affect correctness

### Sample support and local-MRCA truncation

The checked support restriction keeps an edge when its child is a sample or an ancestor of a sample at that coordinate. It preserves sample-ending ancestry. **Fig.3 additionally removes material above local all-sample MRCAs**. Those removed ancestors still have paths to samples, so this is a separate operation. Appendix E's stated tracing algorithm continues to graph roots. [Source: sample resolution and Fig.3](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#iyae100-s3)

### Recovery depends on the observation

Sample-rootward arrays recover the supported relation; all-node arrays can also encode unsupported edges. Preserve node catalogs, sample IDs, persistent internal labels and unary nodes. Equal interval unions need not have equal partition syntax; adjacent fragments may represent the same span as one interval. Canonical serialization is additional work. The existing support criterion and counterexample make the needed Appendix E qualification explicit, without a novelty claim. [Source: Appendix E](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app5)

### Appendix B normalization needs resolution

Primary MathML gives the Big rates:

~~~math
\lambda_k=k\rho,\qquad \mu_k=\binom{k}{2}.
~~~

and the Little effective-link expression:

~~~math
\nu(\mathcal L)=\sum_{x\in\mathcal L}\left(\max_{(\ell,r,a)\in x}r-\min_{(\ell,r,a)\in x}\ell-1\right),\qquad \lambda_{\mathrm{Little}}=\frac{\rho\nu}{m-1}.
~~~

The appendix writes Big event growth as O(exp(rho)) and Little growth as O(rho²), without spelling out the expectation/regime/normalization in that sentence. These are substantive imported mathematical claims. [Source: Appendix B, MathML IM29, UM1, IM31 and IM38–IM42](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app2)

An **unproved occupation-time calculation** starting at two lineages with the literal Big rates suggests:

~~~math
t_j=\frac{2^{j-1}\rho^{j-2}}{j!},\qquad \mathbb E[B]=e^{2\rho}-1,\qquad \mathbb E[N]=2e^{2\rho}-1.
~~~

B would count births/recombinations and N all events before absorption. This requires a valid occupation identity, absorption and integrability. **It is not a checked Lean theorem or a declared erratum.** Resolve the cited Griffiths–Marjoram convention before freezing a bound; common clock scaling preserves birth/death ratios. A separate lane is investigating. No normalization is silently changed.

## Status key

- **Checked scoped result:** the exact limited result has an existing receipt; its whole section may remain incomplete.
- **Partial:** checked related mathematics exists, with a specified missing target.
- **Open:** unformalized mathematical or algorithmic work.
- **Source clarification required:** exact primary theorem/model/convention must be resolved.
- **Empirical reproduction open:** data/software evidence is needed.
- **Research agenda:** source asks a question rather than asserting its answer.
- **Context documented:** history accounted for, imported models explicitly distinguished.

No percentage of the paper proved is calculated: a definition and an asymptotic probability theorem are different work units.

## Source-to-claim index

| ID | Claim family | Current status | Source / journal pages |
|---|---|---|---|
| M01 | Finite interval gARG | checked scoped result | [Genome ARGs](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#iyae100-s1), 2 |
| M02 | Genome bounds, dates, owners and metadata | partial | [Genome ARGs](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#iyae100-s1), 2 |
| M03 | Multiple crossovers and gene conversion | open | [Genome ARGs](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#iyae100-s1), 2 |
| M04 | Classical event arity and parent ordering | partial | [Event ARGs](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#iyae100-s2), 2, 3 |
| M05 | Lossless event encoding before simplification | checked scoped result | [Ancestral material and sample resolution](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#iyae100-s3), 3, 4 |
| M06 | Sample-support restriction | checked scoped result | [Ancestral material and sample resolution](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#iyae100-s3), 3, 4 |
| M07 | Fig.3 local-MRCA truncation | open | [Ancestral material and sample resolution](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#iyae100-s3), 4 |
| M08 | Tables and incremental local-tree recovery | partial | [Implementation and efficiency](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#iyae100-s5), 5 |
| M09 | Unresolved event order in coarse topology | open | [Discussion](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#iyae100-s6), 5, 6, 7 |
| M10 | Recombination detectability | source clarification required | [A diversity of structures](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#iyae100-s4), 5 |
| M11 | Tree-metric costs and overlooked shared identity | source clarification required | [Discussion](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#iyae100-s6), 6, 7 |
| M12 | Scalability, software use and standardization | empirical reproduction open | [Implementation and efficiency](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#iyae100-s5), 5, 6, 7 |
| M13 | Uncertainty and improved global benchmarks | research agenda | [Discussion](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#iyae100-s6), 5, 6, 7 |
| A01 | Big/Little common-observable law | open | [Ancestral graphs: a brief history](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app1), 11, 12 |
| A02 | NP-hard minimum recombination reconstruction | source clarification required | [Ancestral graphs: a brief history](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app1), 11, 12 |
| A03 | Coalescent, ASG and inference history | context documented | [Ancestral graphs: a brief history](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app1), 11, 12 |
| B01 | Little-ARG lineage state | open | [The big and little ARG](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app2), 12, 13 |
| B02 | Effective links and splitting | open | [The big and little ARG](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app2), 12, 13 |
| B03 | Merge and retire fully-coalesced material | open | [The big and little ARG](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app2), 12, 13 |
| B04 | Big-ARG generator and event recording | open | [The big and little ARG](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app2), 12, 13 |
| B05 | Big nonexplosion and almost-sure absorption | open | [The big and little ARG](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app2), 12, 13 |
| B06 | Little-ARG absorption | open | [The big and little ARG](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app2), 12, 13 |
| B07 | Big exponential event growth | source clarification required | [The big and little ARG](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app2), 12, 13 |
| B08 | Little quadratic event growth | source clarification required | [The big and little ARG](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app2), 12, 13 |
| B09 | Timed lineage/link counts and likelihood | partial | [The big and little ARG](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app2), 12, 13 |
| B10 | Extrinsic paired-parent timing convention | open | [The big and little ARG](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app2), 12, 13 |
| C01 | Matrix moves and along-genome SPR | open | [Survey of ARG inference methods](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app3), 13, 14 |
| C02 | Monte Carlo, approximations and consensus | source clarification required | [Survey of ARG inference methods](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app3), 13, 14 |
| C03 | Historical inference scalability | empirical reproduction open | [Survey of ARG inference methods](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app3), 13, 14 |
| D01 | Cell-lineage tagging and owner projection | partial | [Cell lineages and ARGs](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app4), 14 |
| D02 | Mutation information resolving cellular bifurcations | open | [Cell lineages and ARGs](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app4), 14 |
| E01 | Executable sample-to-root extraction | checked scoped result | [ARGs and local trees](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app5), 14, 15 |
| E02 | Local-array reconstruction | partial | [ARGs and local trees](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app5), 14, 15 |
| E03 | Executable finite interval serialization | partial | [ARGs and local trees](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app5), 14, 15 |
| E04 | Information loss from unlabelled or suppressed trees | partial | [ARGs and local trees](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app5), 15 |
| E05 | NP-hard SPR reconstruction | source clarification required | [ARGs and local trees](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app5), 15 |
| E06 | SPR with shared internal identities | research agenda | [ARGs and local trees](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app5), 15 |
| F01 | Local arity bounds and presence | checked scoped result | [Locally unary nodes](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app6), 15, 16 |
| F02 | Locally unary examples and sampled ancestors | open | [Locally unary nodes](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app6), 15, 16 |
| G01 | Wright-Fisher generation of the example | open | [Levels of simplification](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app7), 16, 17 |
| G02 | Span and coalescent fraction | open | [Levels of simplification](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app7), 16, 17 |
| G03 | Diamonds and super-diamonds | partial | [Levels of simplification](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app7), 16, 17 |
| G04 | Remove vertices that never coalesce locally | partial | [Levels of simplification](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app7), 16, 17 |
| G05 | Coordinate-dependent unary bypass | partial | [Levels of simplification](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app7), 16, 17 |
| G06 | Adjacent equal-output coalescing | open | [Levels of simplification](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app7), 16, 17 |
| G07 | External simplify implementations | empirical reproduction open | [Levels of simplification](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app7), 16, 17 |
| H01 | Supported diamond loses breakpoint information | checked scoped result | [Precision of recombination information](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app8), 17 |
| H02 | Timing and lineage precision loss | partial | [Precision of recombination information](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app8), 17 |
| H03 | Literal Figure 5 tree counts and boundaries | empirical reproduction open | [Precision of recombination information](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app8), 17 |
| I01 | Four inference outputs and exact inputs | empirical reproduction open | [Example inferred ARGs](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app9), 17, 18 |
| I02 | Seven-recombination parsimony optimum | source clarification required | [Example inferred ARGs](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app9), 18 |
| I03 | Figure 4 metrics and persistent clade claims | empirical reproduction open | [Example inferred ARGs](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app9), 18 |

## Exact proof and reproduction contracts

### M01 — Finite interval gARG

**Source:** [Genome ARGs](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#iyae100-s1), journal pages 2. **Type:** definition. **Status:** checked scoped result.

**Claim.** Finite genome identifiers and samples; acyclic topology; child/parent records annotated by disjoint inherited intervals.

**Existing evidence.** WongGARG.GARG, Interval, EdgeRecord; locus_acyclic and topology_iff_erased.

**Remaining target.** No further gap for the permissive foundation. Keep source child-first tuples distinct from Lean parent-to-child edges.

**Assumptions and boundary.** Finite nodes; shared ordered coordinates. Unique local parents, nonempty annotations and canonical records are separately visible.

**Completion test.** Definition/source correspondence and existing receipt remain explicit.

### M02 — Genome bounds, dates, owners and metadata

**Source:** [Genome ARGs](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#iyae100-s1), journal pages 2. **Type:** model and interpretation. **Status:** partial.

**Claim.** Persistent identifiers are not dates; edges may skip generations; genomes and organism owners differ.

**Existing evidence.** GARG.exists_finite_topological_numbering and conditional GARG.locus_path_projects; older HistoryProjection adapter.

**Remaining target.** Add bounded-genome presentation for formulas using L and a concrete cell/pedigree owner map satisfying compatibility; preserve node/sample identities.

**Assumptions and boundary.** Specify genome domain, time direction, ploidy and skipped generations; same-owner projection may be equality.

**Completion test.** Checked concrete adapter with empirical biological assumptions identified.

### M03 — Multiple crossovers and gene conversion

**Source:** [Genome ARGs](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#iyae100-s1), journal pages 2. **Type:** representation theorem. **Status:** open.

**Claim.** Interval annotation can represent homologous recombination, including multiple crossovers and gene conversion.

**Existing evidence.** Finite interval unions exist; checked event encoding is single crossover.

**Remaining target.** Encode a finite partition with a selected parent per cell; prove routing equivalence; instantiate two-cut gene conversion and multiple crossovers.

**Assumptions and boundary.** Shared coordinate space, no structural variation, unique local parent on support.

**Completion test.** Generic finite mosaic theorem and named examples; no universal biological validation.

### M04 — Classical event arity and parent ordering

**Source:** [Event ARGs](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#iyae100-s2), journal pages 2, 3. **Type:** representation theorem. **Status:** partial.

**Claim.** Classical internal nodes encode merger or crossover events; cutoff alone leaves left/right parent identity ambiguous.

**Existing evidence.** WongEventEncoding plus integrated WongEventDecoding: strict classical degree signatures, executable decodeKind, encoded degree/kind recovery, uniqueness of event-kind map and agreement of designated samples with sample kinds. Equal-parent crossover collision shows why distinct-parent normalization matters.

**Integrated modules:** [WongEventDecoding](../../../real/WongEventDecoding.lean).

**Mapped registered endpoints:** `WongEventDecoding.equal_parent_crossover_same_local`; `WongEventDecoding.kind_signature_injective`; `WongEventDecoding.decode_kind_signature`; `WongEventDecoding.encoded_degrees`; `WongEventDecoding.encoded_kind_recovered`; `WongEventDecoding.classical_kind_unique`; `WongEventDecoding.classical_encoded_sample_iff`.

**Remaining target.** The strict ClassicalShape is a supplied proof of degree validity, not a total executable validator for arbitrary graphs. Its signatures are sample(1,0), merger(1,2), recombination(2,1), terminal root(0,2). Broader root/sample exceptions and an explicit forgotten-left/right-order collision remain separate.

**Assumptions and boundary.** Fixed node IDs and positive span; proper interior cuts; distinct crossover parents. Strict shape excludes isolated samples, pass-through nodes, multiple crossovers and multifurcations; it is not imposed on all gARGs.

**Completion test.** Integrated strict-shape encoding/decoding is checked. A general validator/exception extension or omitted-order witness requires its own exact statement; preserve current scope.

### M05 — Lossless event encoding before simplification

**Source:** [Ancestral material and sample resolution](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#iyae100-s3), journal pages 3, 4. **Type:** representation theorem. **Status:** checked scoped result.

**Claim.** First-stage conversion duplicates topology and labels edges by full span or complementary intervals; event information is recoverable.

**Existing evidence.** Integrated WongEventDecoding proves normalized_same_local_iff, normalized_records_injective, encode_decode, decode_encode, Graph.parents_identified, Graph.graph_identified and Graph.encoded_canonical; left/right parents and cut are recovered.

**Integrated modules:** [WongEventDecoding](../../../real/WongEventDecoding.lean).

**Mapped registered endpoints:** `WongEventDecoding.crossover_left_identified`; `WongEventDecoding.crossover_right_identified`; `WongEventDecoding.normalized_same_local_iff`; `WongEventDecoding.normalized_records_injective`; `WongEventDecoding.encode_decode`; `WongEventDecoding.decode_encode`; `WongEventDecoding.Graph.parents_identified`; `WongEventDecoding.Graph.graph_identified`; `WongEventDecoding.Graph.encoded_canonical`; `WongEventDecoding.same_local_of_records_eq`.

**Remaining target.** Mathematical first-stage inverse is closed on the explicit normalized encoding range. Executable recognition/parsing of arbitrary records, timestamps and external metadata are not supplied by this theorem; they must be preserved separately if added to the input model.

**Assumptions and boundary.** Fixed node type/IDs and known positive span; root/single-parent/crossover ParentSpec; distinct crossover parents and interior cuts. EncodedRecords includes an explicit range witness. decode uses Classical.choose; raw conversion precedes sample restriction.

**Completion test.** The source's scoped lossless parent-specification conversion has an integrated receipt. Do not describe the classical range inverse as an executable universal event parser or claim recovery after simplification.

### M06 — Sample-support restriction

**Source:** [Ancestral material and sample resolution](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#iyae100-s3), journal pages 3, 4. **Type:** algorithmic semantics. **Status:** checked scoped result.

**Claim.** Trace sample ancestry at each coordinate to identify supported inheritance.

**Existing evidence.** AncestralRestriction locus_sample_path_iff, restriction_idempotent, restriction_nested, restriction_union_iff, indexed_recovery_iff; WongGARG.extracted_eq_local_iff_sampleSupported.

**Remaining target.** Preserve the exact operation name. It keeps ancestors above local MRCAs, unlike M07.

**Assumptions and boundary.** Fixed-locus paths and retained sample/node catalog.

**Completion test.** Keep exact support criterion and raw unsupported-edge counterexample.

### M07 — Fig.3 local-MRCA truncation

**Source:** [Ancestral material and sample resolution](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#iyae100-s3), journal pages 4. **Type:** algorithmic semantics. **Status:** open.

**Claim.** Fig.3 omits entirely coalesced material and the grand MRCA Q after all local genealogies coalesce below it.

**Existing evidence.** ExtractedAt and SampleSupported keep every ancestor of a sample; they do not implement this extra removal.

**Remaining target.** Track descendant sample sets/counts, truncate above local all-sample MRCAs and prove exactly which retained ancestry/MRCA facts survive.

**Assumptions and boundary.** Unique local parent; connected sample genealogy for all-sample MRCA; explicit forest, zero-sample and one-sample cases.

**Completion test.** Checked MRCA truncation and relevant example; no false preservation of paths from removed ancestors.

### M08 — Tables and incremental local-tree recovery

**Source:** [Implementation and efficiency](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#iyae100-s5), journal pages 5. **Type:** algorithmic complexity. **Status:** partial.

**Claim.** Succinct tree sequences use node/edge and site/mutation tables and efficiently recover consecutive local trees and differences.

**Existing evidence.** Finite cell semantics are checked. WongMemoizedTracing now adds run_write_accounting, run_cost_bounds and memoized_cost_bounds: each nonempty cache entry is written once; checks/lookups are bounded by writes plus sample-list length.

**Integrated modules:** [WongMemoizedTracing](../../../real/WongMemoizedTracing.lean).

**Mapped registered endpoints:** `WongMemoizedTracing.run_write_accounting`; `WongMemoizedTracing.run_cost_bounds`; `WongMemoizedTracing.memoized_cost_bounds`.

**Remaining target.** Define executable sorted tables and across-coordinate remove/insert updates, prove equivalence to direct extraction and analyze record scanning, functional-cache evaluation, actual array allocation and machine costs. The new per-coordinate abstract count theorem does not prove those costs.

**Assumptions and boundary.** For the count inequalities, even cycles or insufficient fuel are allowed; correctness additionally needs finite acyclic input and sufficient fuel. Functional cache updates and parent lookup are not assumed constant time. Sites/mutations remain a separately specified table extension.

**Completion test.** Abstract per-coordinate counts are now checked. Sequential-across-genome update correctness and a concrete representation/runtime cost model remain required.

### M09 — Unresolved event order in coarse topology

**Source:** [Discussion](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#iyae100-s6), journal pages 5, 6, 7. **Type:** representation theorem. **Status:** open.

**Claim.** Polytomies and multiple-parent nodes aggregate unresolved coalescence/recombination order.

**Existing evidence.** Fixed-node contraction permits aggregate outputs, without an event-refinement interpretation.

**Remaining target.** Define valid refinements and observation fibres; construct different event orders with one coarse gARG.

**Assumptions and boundary.** Intermediate event identities are omitted; a refinement set is not a posterior probability.

**Completion test.** Checked refinement examples and precise preserved/lost observations.

### M10 — Recombination detectability

**Source:** [A diversity of structures](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#iyae100-s4), journal pages 5. **Type:** imported probabilistic/statistical result. **Status:** source clarification required.

**Claim.** Only some recombinations change topology and a smaller subset is detectable under specified mutation/rate models.

**Existing evidence.** Graph collisions do not establish these probabilities or statistical detection bounds.

**Remaining target.** Retrieve exact primary propositions; define probability model, observable sequences, event classes, rates and sample-size regime; prove the specific result.

**Assumptions and boundary.** Model-specific coalescent and mutation assumptions; no universal DNA/species conclusion.

**Completion test.** Exact theorem and checked dependency, or explicit imported gap; no substitution of generic nonidentifiability.

**Article reference locators:** [iyae100-B49](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#iyae100-B49). These identify attribution, not an independent proof audit of every cited work.

### M11 — Tree-metric costs and overlooked shared identity

**Source:** [Discussion](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#iyae100-s6), journal pages 6, 7. **Type:** imported complexity and observation claim. **Status:** source clarification required.

**Claim.** Some standard tree comparisons are quadratic or worse; treewise evaluation can miss cross-tree persistence.

**Existing evidence.** No specific metric cost theorem or cross-tree-identity collision is registered.

**Remaining target.** Choose the actual metric/algorithm and prove its cost; separately give equal local observations with different shared internal identities.

**Assumptions and boundary.** Do not quantify over all tree metrics; upper bound, lower bound and empirical runtime differ.

**Completion test.** Specific cost theorem and formal observation example.

### M12 — Scalability, software use and standardization

**Source:** [Implementation and efficiency](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#iyae100-s5), journal pages 5, 6, 7. **Type:** software and empirical. **Status:** empirical reproduction open.

**Claim.** Article reports tskit applications/efficiency and recommends shared software infrastructure.

**Existing evidence.** Lean graph semantics do not certify software binaries or speedups.

**Remaining target.** Record historical versions, cited benchmarks and interoperability examples; document recommendation as judgment.

**Assumptions and boundary.** Article-era software/data; full external implementation verification is a separate project.

**Completion test.** Dated evidence or clearly unreplicated primary support; no formal-software-certification claim.

### M13 — Uncertainty and improved global benchmarks

**Source:** [Discussion](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#iyae100-s6), journal pages 5, 6, 7. **Type:** research agenda. **Status:** research agenda.

**Claim.** Node-age/breakpoint uncertainty, downstream propagation, global metrics and realistic pedigree benchmarks are future work.

**Existing evidence.** No solutions claimed.

**Remaining target.** Keep explicit source open-question inventory and needed definitions; assess any new theorem independently.

**Assumptions and boundary.** Research questions are not established claims or automatically required new discoveries.

**Completion test.** Faithful documented agenda with no invented completion claim.

### A01 — Big/Little common-observable law

**Source:** [Ancestral graphs: a brief history](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app1), journal pages 11, 12. **Type:** imported stochastic equivalence. **Status:** open.

**Claim.** Hudson and Griffiths formulations describe equivalent recombinant ancestry while their processes and graphs differ.

**Existing evidence.** No coupling or probability-law model.

**Remaining target.** Define both processes with matched parameters and prove equality in law of named sample ancestry/local-tree observables.

**Assumptions and boundary.** Same sample/genome/rate/clock conventions; explicit irrelevant-event projection and MRCA stopping.

**Completion test.** Law equivalence of the chosen observation, not full event-graph distributions.

**Article reference locators:** [iyae100-B56](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#iyae100-B56), [iyae100-B34](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#iyae100-B34). These identify attribution, not an independent proof audit of every cited work.

### A02 — NP-hard minimum recombination reconstruction

**Source:** [Ancestral graphs: a brief history](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app1), journal pages 11, 12. **Type:** imported complexity theorem. **Status:** source clarification required.

**Claim.** General parsimonious reconstruction is NP-hard, attributed to Wang et al. 2001.

**Existing evidence.** No sequence-matrix model, complexity problem or reduction.

**Remaining target.** Recover exact decision problem, mutation assumptions, input encoding and threshold; prove polynomial reduction with yes/no equivalence.

**Assumptions and boundary.** Finding a compatible history, finding lower bounds and certifying optimum are different tasks.

**Completion test.** Exact primary theorem and reduction with size/runtime bounds; difficult mathematics remains in scope.

**Article reference locators:** [iyae100-B144](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#iyae100-B144). These identify attribution, not an independent proof audit of every cited work.

### A03 — Coalescent, ASG and inference history

**Source:** [Ancestral graphs: a brief history](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app1), journal pages 11, 12. **Type:** history and imported model semantics. **Status:** context documented.

**Claim.** Overview distinguishes processes, graph realizations, inference approximations and ASG nonuniform tree selection.

**Existing evidence.** Bibliographic taxonomy only; no selection or ASG stochastic model.

**Remaining target.** If claiming mathematical coverage of the ASG description, define random graph and tree-selection kernel. Historical mentions do not require proving every cited article.

**Assumptions and boundary.** No transfer of recombination graph proofs to mutation, selection or posterior laws.

**Completion test.** Attribution documented and embedded imported model explicitly unformalized.

### B01 — Little-ARG lineage state

**Source:** [The big and little ARG](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app2), journal pages 12, 13. **Type:** stochastic definition. **Status:** open.

**Claim.** Finite distinct lineages carry disjoint (left,right,sample-count) segments; initially n full-genome segments of count 1.

**Existing evidence.** Finite interval DAG alone is a different state space.

**Remaining target.** Define ordered segment/sample-set state and retired coordinates; prove initialization, sample-partition and mass invariants.

**Assumptions and boundary.** Initially n>=2,m>=2 integer sites,rho>=0; equal-content lineages stay distinct; counts arise from disjoint sample sets.

**Completion test.** Initialization and transition invariants justify sample-count sums <=n.

### B02 — Effective links and splitting

**Source:** [The big and little ARG](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app2), journal pages 12, 13. **Type:** stochastic combinatorics. **Status:** open.

**Claim.** Link count is sum of max(right)-min(left)-1 over lineages, including trapped gaps; recombination rate rho*nu/(m-1).

**Existing evidence.** Exact primary MathML UM1 and IM29 checked; no Lean transition theorem.

**Remaining target.** Enumerate effective links and prove count formula; uniform split preserves exact ancestral segments and counts.

**Assumptions and boundary.** Discrete coordinates, nonempty lineages, proper cuts; eligible links are not only inside material segments.

**Completion test.** Executable link enumeration and split, invariant proof, nonnegative/zero rates.

### B03 — Merge and retire fully-coalesced material

**Source:** [The big and little ARG](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app2), journal pages 12, 13. **Type:** stochastic combinatorics. **Status:** open.

**Claim.** Unordered pairs merge at choose(k,2); overlapping counts add, material of count n is retired.

**Existing evidence.** MathML IM31 and IM34-IM36 verified; no transition semantics.

**Remaining target.** Prove canonical overlay, additive overlap, preserved nonoverlap and correct retirement/empty-lineage deletion.

**Assumptions and boundary.** Disjoint sample-set invariant, distinct pair and half-open endpoints; subset coalescence does not retire material.

**Completion test.** Valid transitions preserve sample genealogy and record the local MRCA correctly.

### B04 — Big-ARG generator and event recording

**Source:** [The big and little ARG](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app2), journal pages 12, 13. **Type:** stochastic definition. **Status:** open.

**Claim.** At k lineages rates are choose(k,2) mergers and k*rho recombinations; stop at 1.

**Existing evidence.** MathML IM38/IM39 verified; event encoding is not a probability kernel.

**Remaining target.** Construct continuous-time jump process or exponential-holding sampler and prove finite event-graph prefix validity.

**Assumptions and boundary.** Finite rho and n; absorbing 1; explicit discrete/continuous breakpoint distribution and time units.

**Completion test.** Well-defined kernel and valid event records.

### B05 — Big nonexplosion and almost-sure absorption

**Source:** [The big and little ARG](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app2), journal pages 12, 13. **Type:** probability theorem. **Status:** open.

**Claim.** The source asserts finite-time arrival at the grand MRCA, citing quadratic merger versus linear branching.

**Existing evidence.** No stochastic termination theorem; finite traversal bounds are unrelated.

**Remaining target.** Prove nonexplosion and almost-sure finite hitting time of 1; establish integrability needed for expectations.

**Assumptions and boundary.** lambda_k=k*rho, mu_k=k(k-1)/2; finite initial k/rho; absorbing 1.

**Completion test.** Probability theorem, not deterministic termination of every random execution.

### B06 — Little-ARG absorption

**Source:** [The big and little ARG](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app2), journal pages 12, 13. **Type:** probability theorem. **Status:** open.

**Claim.** Every coordinate eventually coalesces and active lineages disappear.

**Existing evidence.** No stochastic proof; recombination increases lineage count.

**Remaining target.** Prove nonexplosion and almost-sure retirement of all coordinates, directly or via a justified coupling.

**Assumptions and boundary.** Initial finite discrete genome/sample/rate; continuum extension separate.

**Completion test.** Almost-sure theorem with explicit regime, not a decreasing-lineage ranking argument.

### B07 — Big exponential event growth

**Source:** [The big and little ARG](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app2), journal pages 12, 13. **Type:** imported asymptotic theorem. **Status:** source clarification required.

**Claim.** The article writes O(exp(rho)) events to grand MRCA and cites Griffiths-Marjoram 1997.

**Existing evidence.** Exact MathML IM41; no formal cost variable or bound.

**Remaining target.** Resolve expectation, event type, asymptotic regime and rate convention. Literal rates suggest a factor-of-two exponential mismatch; prove the correctly matched result.

**Assumptions and boundary.** Fix n>=2, random cost, absorption/integrability and rho normalization; time rescaling leaves birth/death ratio unchanged.

**Completion test.** Matched primary result and proved bound; no silent replacement of exp(rho) with exp(2*rho).

**Article reference locators:** [iyae100-B34](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#iyae100-B34). These identify attribution, not an independent proof audit of every cited work.

### B08 — Little quadratic event growth

**Source:** [The big and little ARG](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app2), journal pages 12, 13. **Type:** imported asymptotic theorem. **Status:** source clarification required.

**Claim.** The article writes O(rho^2) simulation events, citing Hein 2004 and Baumdicker2022.

**Existing evidence.** Exact MathML IM42; no cost proof.

**Remaining target.** Find precise bound, expectation and discrete/continuous regime; state dependence on n,m,rho and event types; prove it.

**Assumptions and boundary.** Matched normalization and constants; runtime also needs controlled per-event cost.

**Completion test.** Explicit theorem in declared regime or unresolved imported gap.

**Article reference locators:** [iyae100-B49](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#iyae100-B49), [iyae100-B5](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#iyae100-B5). These identify attribution, not an independent proof audit of every cited work.

### B09 — Timed lineage/link counts and likelihood

**Source:** [The big and little ARG](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app2), journal pages 12, 13. **Type:** likelihood and identifiability. **Status:** partial.

**Claim.** Rates require k(t),nu(t); a gARG may leave recombination time and grouping ambiguous.

**Existing evidence.** WongTimedHistory proves a concrete family of valid timed seven-node event graphs: omission of the recombination node gives exactly the same observed six-node interval gARG and retained dates, while event times 2 and 4 produce actual crossing-edge lineage counts 4 and 3 at time 3. Exact time/count decoders are ruled out on this family.

**Integrated modules:** [WongTimedHistory](../../../real/WongTimedHistory.lean).

**Mapped registered endpoints:** `WongTimedHistory.raw_chronology`; `WongTimedHistory.raw_event_arities`; `WongTimedHistory.observed_represents_contraction`; `WongTimedHistory.observed_dates_independent`; `WongTimedHistory.observed_chronology`; `WongTimedHistory.observation_independent`; `WongTimedHistory.counted_edge_iff`; `WongTimedHistory.hidden_times_differ`; `WongTimedHistory.lineage_counts_differ`; `WongTimedHistory.sample_date_is_not_event_date`; `WongTimedHistory.no_exact_time_decoder`; `WongTimedHistory.no_exact_lineage_decoder`.

**Remaining target.** The deterministic timing/lineage collision is closed for this specified observation. Define the full stochastic model, piecewise effective-link counts, rate/likelihood function and data laws before claiming likelihood results; the witness does not prove likelihood equality or general statistical impossibility.

**Assumptions and boundary.** Backward natural-number dates, strict chronological edges, strict binary event arities, explicit local contraction and retained-ID embedding. Count interpretation is before terminal-root time 10; no continuing post-root absorbing lineage is asserted.

**Completion test.** The explicit no-decoder witness is checked. Source likelihood and continuous-time process claims remain separate B01-B10 obligations.

### B10 — Extrinsic paired-parent timing convention

**Source:** [The big and little ARG](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app2), journal pages 12, 13. **Type:** representation theorem. **Status:** open.

**Claim.** Paired parental genomes at recombination time and grouping conventions can restore lineage splitting and trapped links.

**Existing evidence.** No timed grouping decoder.

**Remaining target.** Define enriched timed nodes and grouping; prove recovery of event partition and k(t),nu(t), including gaps.

**Assumptions and boundary.** Basic coalescent, paired identities/times, ordered routing; not arbitrary gARG topology.

**Completion test.** Sufficient-data inverse plus failure when the convention is omitted.

### C01 — Matrix moves and along-genome SPR

**Source:** [Survey of ARG inference methods](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app3), journal pages 13, 14. **Type:** imported algorithms. **Status:** open.

**Claim.** Parsimony methods use sequence row/column moves or successive tree rearrangements.

**Existing evidence.** No sequence-state semantics or reconstruction algorithms.

**Remaining target.** Define named mutation/coalescence/recombination moves and prove compatibility of constructed ARGs; formalize event-to-SPR relation including invisible events.

**Assumptions and boundary.** Mutation model, finite matrix encoding, rooting and moves explicit; heuristics do not certify optima.

**Completion test.** Sound move semantics for claimed algorithm families; hardness is A02, software reproduction separate.

### C02 — Monte Carlo, approximations and consensus

**Source:** [Survey of ARG inference methods](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app3), journal pages 13, 14. **Type:** imported statistical algorithms. **Status:** source clarification required.

**Claim.** Methods average over ARGs or approximate models; consensus uses breakpoint frequency threshold k plus extra filters and local consensus trees.

**Existing evidence.** No target posterior, invariant sampler law or exact consensus rule.

**Remaining target.** Obtain precise primary target/approximation and filtering/consensus rules for any claimed formal coverage; prove a clearly named property.

**Assumptions and boundary.** A sampled cloud is not all compatible histories; graph validity does not prove sampler correctness.

**Completion test.** Specified algorithm/property or explicit unformalized imported description; not an implied proof of every listed package.

### C03 — Historical inference scalability

**Source:** [Survey of ARG inference methods](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app3), journal pages 13, 14. **Type:** empirical review. **Status:** empirical reproduction open.

**Claim.** Article gives practical dataset-size limits and an article-era scalability ranking.

**Existing evidence.** No independent benchmark evidence in Lean receipts.

**Remaining target.** Record historical versions, hardware, sample/sequence sizes and cited experiments; reproduce if asserting independent confirmation.

**Assumptions and boundary.** Historical publication context; runtime and accuracy are empirical.

**Completion test.** Dated evidence with limitations, not a current ranking.

### D01 — Cell-lineage tagging and owner projection

**Source:** [Cell lineages and ARGs](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app4), journal pages 14. **Type:** model and representation theorem. **Status:** partial.

**Claim.** Genomes can tag the same event above or below it; one child-event node and paired parental-genome nodes are different encodings.

**Existing evidence.** HistoryProjection proves conditional owner path projection; no actual cellular instance.

**Remaining target.** Construct finite diploid cell lineage/pedigree; prove both tag projections and owner compatibility preserve specified ancestry.

**Assumptions and boundary.** Explicit mitosis/meiosis model, ploidy, timing and within-organism equality; many-to-one owners allowed.

**Completion test.** Source-grounded example with commuting ancestry maps; no automatic Alexander infinitary transfer.

### D02 — Mutation information resolving cellular bifurcations

**Source:** [Cell lineages and ARGs](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app4), journal pages 14. **Type:** biological and statistical interpretation. **Status:** open.

**Claim.** Schematic polytomies reflect successive bifurcations; informative mutations can in principle distinguish them.

**Existing evidence.** No mutation observation or reconstruction model.

**Remaining target.** Define binary cell lineage and explicit sufficient mutation observations; prove distinction of the relevant branch order and give failures with inadequate data.

**Assumptions and boundary.** Semiconservative duplication is an empirical premise; mutation recurrence/errors/sampling must be specified.

**Completion test.** Conditional sufficient-data result with biological premise attributed; not undefined 'enough mutations'.

### E01 — Executable sample-to-root extraction

**Source:** [ARGs and local trees](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app5), journal pages 14, 15. **Type:** algorithm correctness. **Status:** checked scoped result.

**Claim.** Initialize parent array empty; trace each sample rootward at a coordinate until a root or previously traversed parent entry.

**Existing evidence.** WongSampleTracing and WongRecordTracing verify executable actual-record extraction. WongMemoizedTracing additionally proves cache closure, visited-entry early stopping, completeness, equality to the reference extractor, actual-gARG extraction with fuel equal to node cardinality, and records_to_memoized_sample_array. Persistent node IDs and unary ancestors are retained.

**Integrated modules:** [WongSampleTracing](../../../real/WongSampleTracing.lean), [WongRecordTracing](../../../real/WongRecordTracing.lean), [WongMemoizedTracing](../../../real/WongMemoizedTracing.lean).

**Mapped registered endpoints:** `WongSampleTracing.trace_exact`; `WongSampleTracing.trace_length_le`; `WongSampleTracing.tracedNodes_exact`; `WongSampleTracing.extract_some_iff`; `WongSampleTracing.actual_garg_extraction`; `WongRecordTracing.lookup_sound`; `WongRecordTracing.lookup_complete`; `WongRecordTracing.lookup_represents`; `WongRecordTracing.records_to_sample_array`; `WongMemoizedTracing.visit_complete`; `WongMemoizedTracing.visit_closed`; `WongMemoizedTracing.memoExtract_some_iff`; `WongMemoizedTracing.memoExtract_eq_reference`; `WongMemoizedTracing.run_write_accounting`; `WongMemoizedTracing.run_cost_bounds`; `WongMemoizedTracing.memoized_cost_bounds`; `WongMemoizedTracing.actual_memoized_extraction`; `WongMemoizedTracing.records_to_memoized_sample_array`; `WongMemoizedTracing.memoized_records_round_trip_iff`.

**Remaining target.** The stated sample-rootward algorithm and abstract write/check/lookup counts are checked. Finite canonical interval serialization remains E03/G06; machine-array storage, concrete record-comparison/runtime costs and external tskit conformance remain M08/G07. No local-MRCA truncation is implied.

**Assumptions and boundary.** Finite acyclic gARG, unique local parent, decidable node equality/ordered-coordinate tests, exact record/sample membership enumerations; duplicate and reordered lists are permitted. A root and an unvisited node both have none, so roots may be looked up repeatedly; this is included in the counts.

**Completion test.** Faithful memoized extraction from actual records equals ExtractedAt, using node-count fuel, with standard-axiom verification. Count bounds are abstract operation counts, not constant-time machine operations.

### E02 — Local-array reconstruction

**Source:** [ARGs and local trees](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app5), journal pages 14, 15. **Type:** representation theorem. **Status:** partial.

**Claim.** The paper argues local arrays with spans recover the gARG; tracing samples sees only supported edges unless an extra convention applies.

**Existing evidence.** WongSampleTracing.actual_garg_reconstruction_iff, WongRecordTracing.records_round_trip_iff and WongMemoizedTracing.memoized_records_round_trip_iff prove indexed sample-parent relations equal all original local edges exactly iff SampleSupported. The memoized implementation also agrees extensionally with the reference.

**Integrated modules:** [WongSampleTracing](../../../real/WongSampleTracing.lean), [WongRecordTracing](../../../real/WongRecordTracing.lean), [WongMemoizedTracing](../../../real/WongMemoizedTracing.lean).

**Mapped registered endpoints:** `WongSampleTracing.actual_garg_reconstruction_iff`; `WongRecordTracing.records_round_trip_iff`; `WongMemoizedTracing.records_to_memoized_sample_array`; `WongMemoizedTracing.memoized_records_round_trip_iff`.

**Remaining target.** Both executable reference and memoized indexed-relation reconstruction are closed. A finite interval serializer, canonical record/byte round trip and persistent metadata packaging remain E03/G06; all-node recovery is a different observation.

**Assumptions and boundary.** Unique local parents at every coordinate; exact actual record/sample enumerations; persistent IDs and unary nodes. Equality concerns indexed edge relations, not syntactic interval partitions.

**Completion test.** Receipt covers executable actual-record lookup, cached sample tracing and the semantic iff criterion. Full storage-format serialization remains outstanding.

### E03 — Executable finite interval serialization

**Source:** [ARGs and local trees](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app5), journal pages 14, 15. **Type:** algorithm correctness. **Status:** partial.

**Claim.** Combine coordinate-wise child/parent incidences into edge interval sets.

**Existing evidence.** Integrated WongRecordTracing verifies executable scanning of actual interval records into local parent pointers. Existing BreakpointCells/IntervalNormalization/Simplification provide classical finite interval output.

**Integrated modules:** [WongRecordTracing](../../../real/WongRecordTracing.lean).

**Mapped registered endpoints:** `WongRecordTracing.lookup_sound`; `WongRecordTracing.lookup_complete`; `WongRecordTracing.lookup_represents`.

**Remaining target.** The new module is a reader, not an interval serializer. Implement endpoint sorting, finite cell output, deterministic record grouping and adjacent merging; prove serialization and canonical inverse laws.

**Assumptions and boundary.** Half-open intervals, finite endpoints, deterministic ordering, persistent IDs; no silent loss of isolated nodes or samples.

**Completion test.** Keep executable record lookup marked checked, while finite canonical serialization remains open. Do not conflate those directions.

### E04 — Information loss from unlabelled or suppressed trees

**Source:** [ARGs and local trees](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app5), journal pages 15. **Type:** identifiability theorem. **Status:** partial.

**Claim.** Persistent internal labels and unary nodes carry information conventional local trees may lose; leaf-subset labels vary across coordinates.

**Existing evidence.** Supported diamond proves one contraction/cutoff collision; unsupported-edge example addresses a separate issue.

**Remaining target.** Define the conventional observation and exhibit equal unlabelled trees with different cross-tree identities; separately equal coalescent-only trees with different unary paths.

**Assumptions and boundary.** Distinguish exact arrays, arbitrary isomorphism and leaf-preserving isomorphism.

**Completion test.** Concrete admissible examples and observation equalities for both loss mechanisms.

### E05 — NP-hard SPR reconstruction

**Source:** [ARGs and local trees](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app5), journal pages 15. **Type:** imported complexity theorem. **Status:** source clarification required.

**Claim.** Inferring SPR operations between conventional leaf-labelled trees is NP-hard, citing earlier complexity work.

**Existing evidence.** No formal SPR decision problem or reduction.

**Remaining target.** Select exact rooted/unrooted primary theorem, tree class, labels, moves and threshold; prove polynomial reduction.

**Assumptions and boundary.** Rooted SPR and other tree rearrangement metrics are not interchangeable.

**Completion test.** Exact imported theorem and formal reduction, with size/cost bounds.

**Article reference locators:** [iyae100-B48](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#iyae100-B48), [iyae100-B3](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#iyae100-B3), [iyae100-B9](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#iyae100-B9). These identify attribution, not an independent proof audit of every cited work.

### E06 — SPR with shared internal identities

**Source:** [ARGs and local trees](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app5), journal pages 15. **Type:** research agenda. **Status:** research agenda.

**Claim.** The paper leaves the complexity with partly shared internal nodes unclear.

**Existing evidence.** No solution claimed.

**Remaining target.** State which nodes are shared and which moves are allowed; keep a separate research question.

**Assumptions and boundary.** Conventional NP-hardness does not automatically imply hardness of this variant.

**Completion test.** Explicit problem and source attribution; no assumed solution.

### F01 — Local arity bounds and presence

**Source:** [Locally unary nodes](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app6), journal pages 15, 16. **Type:** combinatorial theorem. **Status:** checked scoped result.

**Claim.** Local children are a subset of graph children; local arity is bounded by graph arity and varies by locus.

**Existing evidence.** WongLocalArity.local_children_subset, local_arity_le_graph_arity, graph_unary_local_zero_or_one, graph_unary_present_locally_unary.

**Remaining target.** Connect executable sample arrays to these counts after E01; preserve distinction between absence and local unary presence.

**Assumptions and boundary.** Finite distinct-child sets and explicit local presence.

**Completion test.** Existing scoped theorem retained; executable-array consequence added if that implementation is claimed.

### F02 — Locally unary examples and sampled ancestors

**Source:** [Locally unary nodes](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app6), journal pages 15, 16. **Type:** examples and representation. **Status:** open.

**Claim.** Graph-binary nodes can be unary wherever present if children inherit disjoint spans; samples can also be unary in longitudinal data.

**Existing evidence.** General arity bounds exist, without all source examples. Integrated WongLocalSimplification additionally protects every sample and proves locally suppressed nodes have at most one original extracted child; it does not supply all named finite examples.

**Integrated modules:** [WongLocalSimplification](../../../real/WongLocalSimplification.lean).

**Mapped registered endpoints:** `WongLocalSimplification.samples_and_branching_representable`.

**Remaining target.** Instantiate varying arity, graph-binary/always-unary, pass-through, recombinant and sampled-ancestor examples; prove counts and safe retention behavior.

**Assumptions and boundary.** Samples need not be leaves; protected unary samples need exceptions to no-unary claims.

**Completion test.** Checked finite examples with correct sample-preservation specification.

### G01 — Wright-Fisher generation of the example

**Source:** [Levels of simplification](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app7), journal pages 16, 17. **Type:** stochastic construction and example. **Status:** open.

**Claim.** Figure 5 comes from a backwards diploid Wright-Fisher simulation with N=10 and two sampled diploid individuals.

**Existing evidence.** No Wright-Fisher parent/split kernel or literal figure-data validation.

**Remaining target.** Define generations, random parent choices, recombination and overlap coalescence; prove finite generated prefixes are gARGs and reproduce the instance separately.

**Assumptions and boundary.** Polytomies and combined common ancestry/recombination are allowed; classical single-event arities do not apply.

**Completion test.** Valid construction and pinned example data; biological adequacy remains empirical.

### G02 — Span and coalescent fraction

**Source:** [Levels of simplification](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app7), journal pages 16, 17. **Type:** quantitative definition. **Status:** open.

**Claim.** Edge width uses interval length; node coalescent span is fraction of sample-reachable span with more than one child.

**Existing evidence.** No measure/length ratio or figure-statistic theorem.

**Remaining target.** Define coordinate measure, local presence, coalescence set and fraction; prove bounds, invariance under partition changes and zero/one cases.

**Assumptions and boundary.** Positive denominator or explicit zero case; sample leaves are distinct from internal ancestors in never-unary descriptions.

**Completion test.** Correct executable discrete/rational or real-measure statistic matching figure shading.

### G03 — Diamonds and super-diamonds

**Source:** [Levels of simplification](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app7), journal pages 16, 17. **Type:** algorithm correctness. **Status:** partial.

**Claim.** Single-entrance/single-exit components can be replaced when intermediate events/genomes are irrelevant to the chosen observation.

**Existing evidence.** AncestryContraction.retained_path_iff; WongDiamond contracted_relation_iff, retained_ancestry_iff, same_finite_output_hides_cutoff.

**Remaining target.** Define exact component recognition and protected boundaries; prove replacement preserves per-locus retained ancestry and re-encode intervals.

**Assumptions and boundary.** Specify lost event IDs/cuts; topology-only single entrance/exit does not authorize ignoring coordinate semantics; protect samples.

**Completion test.** Sound recognizer and arbitrary eligible-component rewrite, not only a four-node witness.

### G04 — Remove vertices that never coalesce locally

**Source:** [Levels of simplification](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app7), journal pages 16, 17. **Type:** algorithm correctness. **Status:** partial.

**Claim.** Nodes unary in every local tree can be removed, increasing parent/child arities of remaining nodes.

**Existing evidence.** Fixed-K contraction exists; integrated WongLocalSimplification derives a coordinate-wise samples-plus-branching predicate, proves it constant on source cells, bounds suppressed nodes to at most one extracted child and isolates unretained nodes locally.

**Integrated modules:** [WongLocalSimplification](../../../real/WongLocalSimplification.lean).

**Mapped registered endpoints:** `WongLocalSimplification.samples_and_branching_cellwise`; `WongLocalSimplification.suppressed_at_most_one_child`; `WongLocalSimplification.unretained_locally_isolated`.

**Remaining target.** The Figure5c stage removes nodes never locally coalescent across the entire genome. Derive and verify that global eligibility rule separately; the new cell-dependent rule targets Figure5d-type contraction and does not itself identify the global stage.

**Assumptions and boundary.** Distinguish absence, roots, sampled ancestors and locally-unary-everywhere; protect designated samples.

**Completion test.** Current coordinate-wise predicate facts are checked. A source-exact global never-coalescent stage with protected samples and aggregate examples remains required.

### G05 — Coordinate-dependent unary bypass

**Source:** [Levels of simplification](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app7), journal pages 16, 17. **Type:** algorithm correctness. **Status:** partial.

**Claim.** Final simplification rewrites edges at coordinates where a globally retained node is unary, while retaining it elsewhere.

**Existing evidence.** Integrated WongLocalSimplification closes coordinate-dependent finite-output existence. It derives source-cell constancy for KeepSamplesAndBranching, returns an actual interval GARG, preserves sample IDs/retained sample ancestry, inherits unique parents, gives SampleSupported and no new breakpoints, and proves unretained nodes locally isolated.

**Integrated modules:** [WongLocalSimplification](../../../real/WongLocalSimplification.lean).

**Mapped registered endpoints:** `WongLocalSimplification.contraction_congr_both`; `WongLocalSimplification.coordinatePresentation`; `WongLocalSimplification.coordinate_contraction_union_acyclic`; `WongLocalSimplification.automatic_reencoded_local_simplification`; `WongLocalSimplification.samples_and_branching_cellwise`; `WongLocalSimplification.suppressed_at_most_one_child`; `WongLocalSimplification.unretained_locally_isolated`; `WongLocalSimplification.samples_and_branching_representable`.

**Remaining target.** The construction is noncomputable. It does not yet prove retained nonsample nodes are non-unary in the output, derive a complete normal-form/idempotence theorem, implement the rewrite, merge adjacent output cells or reproduce literal Figure 5. M07's full MRCA truncation interpretation also remains separately stated.

**Assumptions and boundary.** Finite gARG and shared ordered coordinates; generic theorem takes a cell-constant K(x), while samples-and-branching instance derives that condition. Samples are always protected; unused node IDs remain in the catalog.

**Completion test.** The arbitrary cell-dependent re-encoding and concrete source-relevant retention instance are integrated. Full no-removable-unary normal form, executable/canonical output and literal source example remain explicit.

### G06 — Adjacent equal-output coalescing

**Source:** [Levels of simplification](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app7), journal pages 16, 17. **Type:** algorithm correctness. **Status:** open.

**Claim.** Neighbouring local trees can become identical after simplification and merge into one interval.

**Existing evidence.** Existing cell grouping can retain redundant endpoints; containment of breakpoints does not eliminate them.

**Remaining target.** Merge adjacent equal parent relations/edge supports; prove semantic preservation, maximal components, canonical deterministic output and idempotence.

**Assumptions and boundary.** Fixed domain/support and persistent IDs; prove the equality relation used for merging.

**Completion test.** Identical semantics yields identical normalized output; no redundant boundary remains.

### G07 — External simplify implementations

**Source:** [Levels of simplification](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app7), journal pages 16, 17. **Type:** software conformance. **Status:** empirical reproduction open.

**Claim.** Article relates simplification to msprime/Hudson and external simplify algorithms.

**Existing evidence.** Lean models selected operations, not external software binaries.

**Remaining target.** Pin software versions/configurations and validate conformance through adapters/examples; full implementation verification is a distinct project.

**Assumptions and boundary.** Same protected samples, unary retention and local-MRCA options.

**Completion test.** Configuration-specific conformance evidence; no unqualified 'verified tskit'.

### H01 — Supported diamond loses breakpoint information

**Source:** [Precision of recombination information](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app8), journal pages 17. **Type:** information-loss theorem. **Status:** checked scoped result.

**Claim.** Diamond removal can hide differing local routes and a recombination breakpoint.

**Existing evidence.** WongDiamond.diamond_cutoff_information_loss and same_finite_output_hides_cutoff.

**Remaining target.** Existing abstract four-node witness covers the loss mechanism; literal position 61 is H03.

**Assumptions and boundary.** Observation is contracted relation or explicitly selected common finite output; automatic serializer equality needs G06.

**Completion test.** Preserve exact checked witness and observation.

### H02 — Timing and lineage precision loss

**Source:** [Precision of recombination information](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app8), journal pages 17. **Type:** information-loss theorem. **Status:** partial.

**Claim.** Removing a node may preserve tree count but lose event time; local unary bypass can also hide a recombination's ancestry.

**Existing evidence.** WongTimedHistory adds an actual dated event-graph collision with a validated contraction, equal retained node dates, different hidden recombination times and different intermediate lineage counts. No arbitrary target annotation is varied independently of the graph; counted_edge_iff ties counts to crossing actual edges.

**Integrated modules:** [WongTimedHistory](../../../real/WongTimedHistory.lean).

**Mapped registered endpoints:** `WongTimedHistory.raw_chronology`; `WongTimedHistory.raw_event_arities`; `WongTimedHistory.observed_represents_contraction`; `WongTimedHistory.observed_dates_independent`; `WongTimedHistory.observed_chronology`; `WongTimedHistory.observation_independent`; `WongTimedHistory.counted_edge_iff`; `WongTimedHistory.hidden_times_differ`; `WongTimedHistory.lineage_counts_differ`; `WongTimedHistory.sample_date_is_not_event_date`; `WongTimedHistory.no_exact_time_decoder`; `WongTimedHistory.no_exact_lineage_decoder`.

**Remaining target.** The selected timing/count nonrecoverability mechanism is closed. General interval-of-possible-times characterizations, loss of recombination ancestry under the final local-unary rewrite, and literal Figure 5 reproduction remain. This small example is not a reproduction of every node of Fig3c or Fig 5.

**Assumptions and boundary.** Hidden time is an actual recombination-node date with 0<time<7, distinct from the sampled genome date 0; observation omits that node entirely and retains dates on its six actual remaining nodes.

**Completion test.** Checked concrete temporal and lineage-count collision, with exact observation and target. Broader source timing-bound and ancestry-loss statements require their own contracts.

### H03 — Literal Figure 5 tree counts and boundaries

**Source:** [Precision of recombination information](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app8), journal pages 17. **Type:** finite example reproduction. **Status:** empirical reproduction open.

**Claim.** Successive examples have 6,5,5,4 local trees; position 61 vanishes, later [44,87) and [87,100) merge and 87 vanishes.

**Existing evidence.** Abstract witnesses do not certify exact Figure 5 data.

**Remaining target.** Load published/supplementary intervals, validate graphs, apply specified transformations and compute counts/lost boundaries.

**Assumptions and boundary.** Count maximal equal local parent arrays under the given persistent-ID observation, not record fragments.

**Completion test.** Reproducible source-linked example; distinguish Lean evaluation and external computation.

### I01 — Four inference outputs and exact inputs

**Source:** [Example inferred ARGs](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app9), journal pages 17, 18. **Type:** empirical and software. **Status:** empirical reproduction open.

**Claim.** Figure 4 uses 11 genomes,43 biallelic SNPs over2.4kb ADH with named historical tools and parameters.

**Existing evidence.** No figure input/output dataset in current proof receipts.

**Remaining target.** Pin paper code/data/output hashes, versions/seeds; parse and validate actual gARGs. Distinguish archived-output validation from inference rerun.

**Assumptions and boundary.** KwARG1.0; ARGweaver-D2019; tsinfer0.3.1; Relate1.1.9; mutation5.49e-9 and recombination2.40463e-9/site/generation; Ne1720600.

**Completion test.** Reproducibility receipt with provenance, not proof inferred graphs are biological truth.

### I02 — Seven-recombination parsimony optimum

**Source:** [Example inferred ARGs](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app9), journal pages 18. **Type:** imported optimization theorem and data fact. **Status:** source clarification required.

**Claim.** Dataset is said to require 7 recombinations under minimal parsimony assumptions, citing Song-Hein 2003.

**Existing evidence.** No matrix/history witness or lower bound.

**Remaining target.** Recover exact data/model; certify a compatible 7-event history and rule out all histories with fewer events using a sound certificate or imported theorem.

**Assumptions and boundary.** Mutation/recombination convention, rooting and included sites explicit; a heuristic 7-event run proves only an upper bound.

**Completion test.** Attainment plus lower bound for exact source data.

**Article reference locators:** [iyae100-B128](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#iyae100-B128). These identify attribution, not an independent proof audit of every cited work.

### I03 — Figure 4 metrics and persistent clade claims

**Source:** [Example inferred ARGs](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app9), journal pages 18. **Type:** finite empirical observations. **Status:** empirical reproduction open.

**Claim.** Examples differ in breakpoints, parent counts, unary nodes, polytomies and persistence of Af-f/Fr-f/Wa-f clade and older edges.

**Existing evidence.** General arity results exist; source outputs are not checked.

**Remaining target.** Compute all named metrics from pinned outputs: shared breakpoints, parent counts, coalescent spans, branch order, persistent nodes/edges and named clade across full span.

**Assumptions and boundary.** Source identifiers case-sensitive; graph parent arity differs from event count; one selected output does not measure method-wide accuracy.

**Completion test.** Reproducible paragraph-mapped metric table and reported mismatches.

## Imported results remain proof obligations

| Imported assertion | Primary attribution | Necessary target |
|---|---|---|
| Big/Little equivalence | Hudson1983a; Griffiths–Marjoram 1997 | Matched stochastic models and law equality of a selected ancestry observation. |
| Big event growth | Griffiths–Marjoram 1997, An ancestral recombination graph, IMA87, pp. 257–270 | Resolve normalization and cost; prove absorption/integrability and correct asymptotic expectation. |
| Little event growth | Hein, Schierup and Wiuf 2004; [Baumdicker et al. 2022](https://doi.org/10.1093/genetics/iyab229) | Exact sample/genome/rate regime, event types and constants. |
| Recombination hardness | [Wang, Zhang and Zhang 2001](https://doi.org/10.1089/106652701300099119) | Precise decision problem, mutation restrictions and polynomial reduction. |
| SPR hardness | [Hein et al. 1996](https://doi.org/10.1016/S0166-218X(96)00062-5), [Allen and Steel 2001](https://doi.org/10.1007/s00026-001-8006-8), [Bordewich and Semple 2005](https://doi.org/10.1007/s00026-004-0229-z) | Exact rooted/unrooted metric/tree class and reduction. |
| Seven-event optimum | Song and Hein 2003, Parsimonious Reconstruction of Sequence Evolution and Haplotype Blocks, pp. 287–302 | Exact dataset/model, seven-event witness and lower bound excluding six. |
| Detection and tree-metric cost | Main-text cited sources | Named statistical model or particular algorithm; generic collisions do not prove quantitative bounds. |

An imported theorem can be an explicit assumption while organizing downstream work; then the result remains conditional and that source claim remains unformalized. A custom axiom does not complete its proof. Accounting for a cited claim does not require proving every theorem in every reference.

## Reproduction and software evidence

The data-availability statement points to [tskit-dev/what-is-an-arg-paper](https://github.com/tskit-dev/what-is-an-arg-paper). Inventory its exact commit, inputs, archived outputs and code before expensive historical inference reruns. Distinguish:

- parsing/validating an archived figure graph;
- verified statistics and simplification calculations;
- reproducing the historical inference run;
- external software conformance to a specification;
- biological truth of the inferred history.

A theorem can certify a statistic on supplied data. It does not make the supplied history biologically correct.

## Documentation corrections for the owning lane

These proposed source-wording corrections concern earlier project notes; this ledger update changes only its two publication documents.

| Existing passage | Clarification |
|---|---|
| notes/WONG-ALEXANDER-BRIDGE-STATUS.md:31 | Distinguish support restriction and Fig.3 above-MRCA truncation. |
| Same file, companion list near line 150 | Use sample-support restriction in the claim that all sample-ending paths survive; full Fig.3 truncation removes some starting vertices. |
| Same file:244 | Use the precise checked operation name for the composition. |
| Same file, historical individual-check paragraph | Add current integrated receipt context, preserving historical receipts. |

WONG-GARG-FOUNDATION already distinguishes SampleSupported, ExtractedAt and all-node parent relations accurately. WONG-SIMPLIFICATION already records fixed retention, noncomputability and missing adjacent coalescing. Preserve those boundaries.

## Completion criteria

**Finite representation/transformation package:** normalized mathematical decoding, actual record extraction and coordinate-dependent finite-output representation now have integrated receipts. Memoized correctness, abstract operation counts and the timed collision are also checked. Complete finite canonical serialization, local-MRCA interpretation, output normal-form/idempotence, adjacent coalescing and source examples. This bounded package still leaves probability expressly pending.

**All asserted mathematical content:** also resolve/prove stochastic equivalence, termination, expectations/asymptotics, quantitative detection/cost claims and imported hardness, or document a precise correction after source resolution. Difficulty is not a reason to reclassify mathematics as narrative.

**Full article coverage:** attach figure/data and software evidence, attribute historical/biological interpretations, and preserve open questions/recommendations. These do not receive artificial theorem certificates.

This inventory is complete at its snapshot. Whole-paper formalization is not complete. No hosted CI, publication, author endorsement or empirical validation is inferred here.

