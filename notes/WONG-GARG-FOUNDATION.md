# Wong genome-ARG foundation and exact local ancestry

**Status:** the complete module compiled successfully with Lean 4.33.1; all ten printed endpoint audits report only standard axioms. Aggregate release integration and independent source-fidelity review are separate checks.

Source: Yan Wong, Anastasia Ignatieva, Jere Koskela, Gregor Gorjanc, Anthony W. Wohns, and Jerome Kelleher (2024), *A general and efficient representation of ancestral recombination graphs*, Genetics 228(1), iyae100. [Published paper](https://doi.org/10.1093/genetics/iyae100); [open published PDF](https://www.pure.ed.ac.uk/ws/portalfiles/portal/458588307/iyae100.pdf). The definition is on journal page 2; local parent pointers and sample-rootward extraction are in Appendix E, pages 14–15.

The source uses finite genome nodes, a designated sample set, and a directed acyclic graph whose parent–child edges carry disjoint genomic intervals. Node identifiers are not birthdates. Appendix E traces inheritance at one genomic position to obtain parent pointers, retaining node identities and unary nodes. This module implements a finite-interval presentation of that representation. The published definition and local-tree interpretation are prior work; no novelty is claimed for them.

## Representation choices

`real/WongGARG.lean` uses generic linearly ordered coordinates, so the interface does not restrict genome coordinates to natural numbers. An interval has endpoints `lo < hi` and means `[lo, hi)`. Each record contains finitely many intervals, with pairwise disjointness of their actual coordinate sets. Adjacent intervals are allowed. Nodes inhabit an arbitrary finite type; genomes, cells, and individuals are not identified with one another by definition.

`GARG.Topology parent child` records the parent-to-child orientation used by the existing Alexander interfaces. Traversing an Appendix E parent pointer runs in the opposite direction. `GARG.AtLocus x parent child` requires one actual record covering `x`. Acyclicity is an explicit structural condition; neither node dates nor chronological ordering of identifiers are assumed.

The following conditions remain separately visible:

- `CanonicalRecords`: at most one stored record per ordered parent–child pair. This is a storage normalization predicate. The path theorems concern the relation represented by all records and do not depend on grouping equivalent annotations into one row.
- `NonemptyAnnotations`: every stored record contains a proper interval. With this premise, and only with it, the topology is exactly the union of all local inheritance relations. Without it, an empty record can be a topological edge with no locus witness.
- `UniqueParentAt x`: at most one inherited parent for a child at this coordinate. This is the single-parent premise for a local oriented forest, not an unstated consequence of arbitrary interval-annotated DAGs.
- `SampleSupported`: every local inheritance edge leads, at that same coordinate, to a designated sample. This distinguishes all annotated local edges from the part visited by tracing sample ancestry.

No coverage of a prescribed genome interval, sample resolution algorithm, mutation model, inferred owner assignment, biological validation, or chronological metadata is smuggled into the base type.

## Mathematical endpoints

| Endpoint | Exact conclusion |
| --- | --- |
| `GARG.locus_path_topology` | Every path at one fixed coordinate is a path in the stored topology. |
| `GARG.locus_acyclic` | Every local relation is acyclic, derived from the stored DAG. |
| `GARG.topology_iff_erased` | Nonempty annotations make topology exactly the locus-erased edge relation. This does not commute erasure with path closure. |
| `GARG.extracted_eq_local_iff_sampleSupported` | Sample-rootward extraction retains all local edges exactly when every edge is sample-supported. |
| `GARG.local_parent_representation` | Under unique local inheritance, `Option Node` parent pointers encode exactly the local edges and have no directed cycles. `none` represents roots without reserving a genome identifier. |
| `GARG.local_ancestors_comparable` | Under the same premise, two ancestors of one child lie in one ancestral chain: they agree, or one reaches the other. |
| `GARG.locus_path_projects` | An actual interval-supported genome path projects to equality or organism ancestry when every stored record has the required owner-to-pedigree compatibility. |
| `GARG.ancestry_constant_without_breakpoint` | Both local edges and their ancestry paths remain identical until an interval endpoint is crossed. This is piecewise constancy, not graph self-similarity. |
| `GARG.natTopology_path_iff` | The bounded natural-number encoding preserves and reflects every nonempty topology path between actual genomes; unused identifiers introduce no paths. |
| `GARG.exists_finite_topological_numbering` | Every finite gARG admits an injective bounded natural-number coding whose edges strictly increase. Identifiers are reordered by a proved construction, not assumed temporal. |

The numbering proof gives an explicit mathematical construction. For `n` nodes, let `A(v)` be the set of strict ancestors and let `id(v)` be any bijection with `Fin n`. Define `code(v) = n * |A(v)| + id(v)`. An edge strictly increases ancestor-set cardinality, and the identifier occupies a block shorter than `n`. The code is injective and below `n²`. Gaps are allowed. The encoded relation `natTopology` contains only edges between actual encoded genomes. Its edges strictly increase and have both endpoints below the bound, and `natTopology_path_iff` proves exact ancestry reflection. This supplies a finite ordered prefix suitable for subsequent completion theorems without asserting that the finite dataset itself is infinite.

## What the bridge now establishes, and what remains

The module makes the existing conditional `HistoryProjection` theorem apply to a source-grounded finite record structure. The owner map and record compatibility still need to be justified for the concrete biological interpretation. Genome steps within one organism may project to equality; genome paths can skip multiple pedigree generations. No injectivity of the owner map is assumed or implied.

The finite breakpoint set consists of all lower and upper interval endpoints. For coordinates `x ≤ y`, if this set has no member in `(x, y]`, the module proves that every local edge and every local ancestry path agrees at `x` and `y`. The half-open boundary convention is part of the theorem. This repeated local structure does not assert scaling, a graph automorphism, or a self-similar infinite population.

The local parent-pointer result is about all annotated edges. Appendix E's sample-rootward extraction is the separate `ExtractedAt` relation. Its equality with all local edges has the exact `SampleSupported` condition above. This prevents a reconstruction claim from silently including material invisible from the selected samples. Equality of local edge semantics also does not by itself imply equality of arbitrary stored interval partitions or duplicate record encodings.

A finite genome DAG alone does not imply an infinite population, Alexander's infinitary ancestry property, a specieslike cluster, or graph self-similarity. Those are separate mathematical properties requiring further hypotheses or completion constructions. This foundation does not formalize the stochastic coalescent, complexity bounds, simplification implementation, benchmark experiments, or every discussion claim in the paper.

## Verification receipt

The root agent ran the serialized compiler against the full module and reported exit code 0 with all ten printed endpoints restricted to `propext`, `Classical.choice`, and `Quot.sound`. Source SHA-256: `D025493EAB6E22742DA87D1F36FD48335198B8BBC0718EB8E20EF13651655016`. Lean version: 4.33.1, with the existing pinned Mathlib environment. A textual scan found no `sorry`, `admit`, or custom axiom declaration. No new dependency download or parallel build was launched by this lane. The per-module receipt does not by itself establish a passing hosted release build or an independent human endorsement.



The compiler lane subsequently normalized line endings to LF without changing proof content. Current source SHA-256 after normalization: D025493EAB6E22742DA87D1F36FD48335198B8BBC0718EB8E20EF13651655016. The fresh aggregate receipt will bind these normalized bytes.

