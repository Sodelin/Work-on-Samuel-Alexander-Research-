# Wong 2024 to Alexander: source coverage and the actual remaining bridge

**The intended source is Yan Wong et al. (2024), _A general and efficient
representation of ancestral recombination graphs_, Genetics 228, iyae100.
The Lean development now includes a finite interval-annotated DAG foundation,
sample-restriction laws, conditional pedigree projection, and a theorem that
an actual finite gARG does not determine infinite whole-population specieslike status. It does
not formalize this entire paper, infer a biological pedigree, or establish that
every projected population is specieslike.**

This source-to-proof audit was made on 25 September 2026 from the
[published version of record](https://www.pure.ed.ac.uk/ws/portalfiles/portal/458588307/iyae100.pdf)
([DOI](https://doi.org/10.1093/genetics/iyae100)). Page references below are
**printed journal pages**. The downloaded PDF has an extra repository cover,
so journal page 2 is the third PDF page. The relevant main text and Appendices
A–I were inspected, with particular attention to E, G and H. The source is
open access under CC BY 4.0. New mathematical deductions and proposed proof
contracts below are our analysis, not quotations or claims of new priority.

This note supersedes the unresolved-source discussion in
[SELF-SIMILARITY-SCOPE](SELF-SIMILARITY-SCOPE.md). Wong's paper is now identified;
the Thue–Morse recursion and the separate avoidance/specieslike bridge are
different parts of the project.

## What the source actually supplies

| Source location | Content | Formalization obligation and status |
|---|---|---|
| Genome ARGs, p. 2; Fig. 1, p. 3 | A finite directed acyclic graph of haploid-genome nodes, a sample subset, and child/parent edges annotated with inherited genomic intervals. One graph edge may span several generations. Genome nodes and organism-pedigree nodes are different objects. | Define finite node and sample types, a coordinate domain, normalized or extensional interval annotations, and acyclicity. WongGARG now checks this foundation over an arbitrary shared linearly ordered coordinate type. Storage normalization and unique local parents are separately visible conditions. |
| Event ARGs, pp. 2–3; conversion, pp. 3–4 | Common-ancestor and crossover events can be encoded by full-genome or left/right inheritance intervals. An ordered choice of the two recombination parents is necessary. | WongEventEncoding gives exact ordered event-parent to interval-gARG conversion, topology/local routing/path correspondence, and cutoff recovery for distinct fixed ordered parents. Full event-metadata storage decoding and classical child-arity validation are separate. |
| Ancestral material and sample resolution, pp. 3–4 | Sample resolution removes material irrelevant to the chosen samples; a raw prospective gARG may contain such material. | Specify which edge-position incidences are visible by tracing from samples. Prove exact reconstruction on the supported relation, and state the condition for equality with the original. AncestralRestriction.indexed_recovery_iff and WongGARG.GARG.extracted_eq_local_iff_sampleSupported now check the exact relation-level criterion. |
| Appendix D, p. 14 | Genome nodes may mark different cellular stages inside one individual; different choices encode events differently. | A biologically justified owner map can identify several genome nodes. Within-organism equality and multi-generation pedigree ancestry must both be allowed. The generic path projection is checked; the biological instance is not. |
| Appendix E, pp. 14–15 | A local tree is represented by a persistent node-indexed parent array. It is extracted by tracing inheritance from samples at a fixed position. Shared internal identities and unary nodes matter to recovery of the ARG. | Under explicit parent uniqueness, WongGARG checks an acyclic all-node parent representation and comparability of ancestors. It also proves exact sample-restricted relation recovery. WongLocalArity proves finite backward-local-walk and parent-array walk bounds. An executable sample-tracing/serialization implementation and runtime cost are not verified. Multiple roots give a forest; one connected tree needs an additional hypothesis. |
| Appendix F, pp. 15–16 | Local arity does not exceed graph arity; an ancestor can be unary in one or every local tree. | WongLocalArity proves the distinct-child subset/cardinality bound and exactly distinguishes a globally unary node being locally absent versus locally unary. |
| Appendix G, pp. 16–17; Fig. 5, p. 6 | Several different simplifications remove nodes or rewrite intervals. Unary suppression and diamond removal preserve chosen coarser information while losing some event/path details. | AncestryContraction and the actual-gARG wrapper prove retained-node sample ancestry preservation under relation-level node elimination. WongSimplification now derives an actual finite disjoint-interval output from input breakpoints, with inherited local uniqueness and no new endpoints. Adjacent-cell coalescing, coordinate-dependent retention, and correctness of the complete tskit algorithm remain separate. |
| Appendix H, p. 17 | Equal tree counts do not imply equal recombination detail. Simplification can remove breakpoint, lineage and event-timing information. | Supply explicit pairs of admissible histories with equal chosen observations but different targets, then apply the existing recovery obstruction. WongExamples supplies a concrete three-node interval-gARG pair with equal sample-extracted relations and unequal raw topology. WongDiamond adds a fully sample-supported four-node collision with different cutoffs and identical contracted relations. Event-timing observations remain separate. |
| Appendices A–B, pp. 11–13 | The graph data structure is distinguished from stochastic coalescent processes. Event rates, termination and growth estimates concern specified processes, often citing earlier work. | Define probability laws, holding times and cost variables before formalizing these claims. Graph reachability proofs do not establish almost-sure termination, asymptotic expectations or likelihoods. |
| Main discussion, pp. 5–7; Appendices C and I, pp. 13–14, 17–18 | Comparisons among inference tools, observed precision, scalability, uncertainty and proposed software standards. | These are software, empirical or research-agenda claims. Reproduce the cited code/data and specify measured quantities; no theorem about the abstract graph alone proves them. |

The paper is a **Perspectives** article containing definitions, mathematical
arguments, examples, biological interpretations and empirical/software
discussion. “Formalize the paper” should therefore mean a declared coverage
matrix with exact statements and explicit exclusions, not a single claim that
all prose has become a theorem.

## Existing checked endpoints and their actual scope

The current continuation also received individual Lean/axiom PASS reports for
[WongGARG](../real/WongGARG.lean) (10 selected endpoints),
[AncestralRestriction](../lean/SamuelAlexanderResearch/AncestralRestriction.lean)
(11), and
[FiniteHistoryCompletion](../lean/SamuelAlexanderResearch/FiniteHistoryCompletion.lean)
(7). Only the permitted standard axioms were reported. The source statements
were independently inspected in this audit. Aggregate registration and hosted
CI for these new modules remain separate integration checks.

WongGARG adds topology/erasure equivalence under NonemptyAnnotations,
local_parent_representation under UniqueParentAt, local_ancestors_comparable,
exists_finite_topological_numbering, natTopology_path_iff, and
ancestry_constant_without_breakpoint. The last statement says ancestry is
unchanged between coordinates when no annotation endpoint is crossed; it is
not scale symmetry.

The base GARG is intentionally a permissive presentation. CanonicalRecords
rules out duplicate parent-child records but does not merge adjacent intervals;
NonemptyAnnotations rules out empty-annotation topological edges. UniqueParentAt
is the additional biological condition required for local parent pointers.
All nodes use one shared coordinate type, but no fixed genome length or
in-domain bounds are built in. Theorems that need these extra conventions must
request them explicitly. localParent represents all AtLocus edges, whereas
ExtractedAt is the separate sample-restricted relation. No theorem here
certifies the C/Python tskit implementation.

The following statements are present in the four existing core modules and
were included in the earlier core audit. This documentation pass did not
rerun Lean; the authoritative receipts and exact source inventories remain
in the repository's verification directory.

| Lean declaration | What is proved | What must still be supplied for Wong |
|---|---|---|
| [AncestryViews.fixed_index_path_survives](../lean/SamuelAlexanderResearch/AncestryViews.lean) | A path at one fixed index remains a path in the union of all indexed edge relations. | An actual well-formed gARG and its relation at each genomic position. |
| AncestryViews.erased_path_time_increases | If all indexed edges respect one supplied natural-number clock, so do paths after index erasure. | The common clock; acyclicity of a raw record is not proved by declaring one. |
| AncestryViews.erasure_converse_fails; erased_graph_does_not_determine_fixed_index_ancestry | Explicit two-edge examples show that a union path can switch loci, and identical unlabelled graphs can give different fixed-locus ancestry answers. | These are relation examples, not a full input-validation or sample-resolution theorem. |
| [AncestryViews.reach_iff_species_descendant](../lean/SamuelAlexanderResearch/SpeciesAdapter.lean); fixed_index_to_species_descendant | The generic nonempty-path relation agrees with the repository's strict ancestry relation on natural-number vertices. | This identifies relations. It does not transfer population axioms or species predicates. |
| [HistoryProjection.path_projects](../lean/SamuelAlexanderResearch/HistoryProjection.lean); path_projects_strict_of_distinct_owners | Under per-edge owner compatibility, a genome path projects to equal organism owners or organism ancestry; distinct owners exclude equality. | An owner assignment justified by the model, and proof of compatibility with the chosen pedigree. A constant owner map satisfies the equality alternative trivially. |
| HistoryProjection.locus_path_projects; erased_path_projects; interval_record_path_projects | The same conditional projection applies to indexed relations, their union and the minimal interval-list interface. | Disjointness, coordinate bounds, a sample set, parent uniqueness, acyclicity, sample resolution and full gARG semantics are not enforced by that interface. |
| [ObservationPrediction.recoverable_iff_constant_on_fibres](../lean/SamuelAlexanderResearch/ObservationPrediction.lean); collision_obstructs_recovery | A target is exactly recoverable precisely when it is constant on states with the same observation; a collision with different targets forbids exact recovery. | A specific space of valid ARG histories, observation and target. The converse uses classical choice; it is not an executable genomic estimator. |
| ObservationPrediction.exact_predictor_iff; compatible_observations_agree_in_future | Exact deterministic prediction requires the transition to preserve observational equality. | A deterministic transition and its validity on the chosen state space. These are not stochastic coalescent or biological prediction theorems. |

All ancestry relations in these Lean adapters point **ancestor to descendant**.
Wong's edge tuple is written child first, and the extraction algorithm moves
rootwards. The translation must explicitly swap argument order when needed.
Genomic positions are not Alexander's reproductive-role labels: a single
edge may carry several positions, while his simple labelled model allows
one role label per ordered parent-child pair.

## Reconstruction: checked relation theorem and remaining implementation

The relation-level support criterion is now checked. The parent-pointer
representation is also checked for the **all-node** local relation. Their
composition into an executable sample-tracing/serialization algorithm remains
a separate proof contract.

The implemented foundation uses finite nodes and a shared, arbitrary linearly
ordered coordinate type with finitely represented half-open intervals. This
covers the discrete Appendix E setting and also permits real coordinates.
Keep the node catalog and sample set in the encoded data. Write R(x,p,c) for
inheritance from parent p to child c at position x. Parent-pointer theorems
require at most one parent per child/position. The base structure enforces
acyclicity. The finite-output construction now groups disjoint cells per endpoint pair; globally minimal interval segmentation and executable serialization remain separate.

A node c is supported at x if c is a sample or has an R(x)-path to a sample.
The sample-visible relation is:

~~~math
R_S(x,p,c) \iff R(x,p,c)\ \land\
\bigl(c\in S\ \lor\ \exists s\in S,\ c\leadsto_x s\bigr).
~~~

The local parent-array entry for c is its unique parent in this relation, or
none. Reconstructing edges from all arrays gives R_S exactly. Consequently:

~~~math
\operatorname{reconstruct}(\operatorname{extract}_S(R))=R
\quad\Longleftrightarrow\quad
\forall x,p,c,\ R(x,p,c)\Longrightarrow \operatorname{Supported}_S(x,c).
~~~

The equality compares indexed inheritance relations or canonical interval
unions. It cannot recover whether one interval was syntactically stored as
two adjacent records. With all source nodes retained, it also avoids claiming
that a parent array by itself identifies which isolated nodes are samples.

**Why the support condition matters.** With one position, sample s, and
another child c, compare the graph containing only p-to-s with the graph
also containing p-to-c. Both are acyclic and have a unique parent at that
position. Sample tracing from s gives the same array in both, because c is
not on a path to s. The extra edge is not reconstructible. The main text's
distinction between raw and sample-resolved gARGs makes this the natural
boundary to state explicitly.

This is our formal reading of Appendix E's reconstruction argument in the
presence of the extraction procedure it describes. It is not a claim that
the authors overlooked a new theorem. One can alternatively encode the
parent relation for **all** nodes instead of tracing only from samples; that
different observation does recover unsupported edges.

Useful immediate companion claims are:

1. Sample resolution preserves every fixed-locus ancestry path ending at a
   chosen sample.
2. Resolving twice is idempotent.
3. For nested sample sets, resolving first to the larger set and then to the
   smaller set agrees with resolving directly to the smaller set.
4. Equal persistent, unsuppressed local parent arrays determine the same
   sample-visible indexed relation; equal unlabelled or unary-suppressed trees
   need not do so.
5. Removing information cannot improve exact recoverability of a fixed target.

Items 1–3 are now checked by AncestralRestriction.locus_sample_path_iff,
restriction_idempotent and restriction_nested. Its indexed_recovery_iff
checks the relation part of item 4; full sample-array reconstruction and the
specific unary-suppression collision still need their own instance. The fifth
is already available abstractly as
ObservationPrediction.recoverable_from_fine_of_coarse. These closure and
composition statements are **proposed project deductions**; the article
does not state a “semigroup theorem” or a general self-similarity theorem.

## Why the Alexander bridge needs more than reconstruction

A Wong gARG has finitely many nodes. Alexander's population hypotheses are
infinitary. A finite image under an owner map remains finite; relabelling it
with natural numbers does not create an eligible infinite population.
Likewise, every finite cluster satisfies the finite/cofinite descendant
alternative vacuously through the finite branch. That says nothing about an
infinite population's eventual ancestry behavior.

There are two honest routes:

- **An ambient model is supplied.** Embed the finite record into an independently
  specified infinite birth-parenthood model; prove owner compatibility and all
  required population or cluster predicates in that ambient model.
- **An extension is constructed.** Prove that a finite record admits some
  explicitly constructed eligible infinite extension. This is an existence
  theorem about a mathematical completion, not reconstruction of an actual
  future population or evidence that the observed organisms form a species.

Different infinite completions can agree on every old edge and old
reachability fact while differing on IAP and whole-population specieslike
status. The checked endpoint
FiniteHistoryCompletion.finite_history_does_not_determine_species constructs
two connected, locally finite, finite-root, natural-date completions of any
ordered finite prefix. One whole graph is an inspecies and maximal specieslike;
the other fails whole-graph IAP. The latter can still contain proper specieslike
subsets. The construction does not preserve a diploid parent bound or provide
reproductive-role labels, and it does not infer actual biological futures.

For a proposed map or completion, the actual proof obligations are:

| Desired conclusion | Required evidence |
|---|---|
| Genome ancestry implies organism ancestry | Owner compatibility for every represented inheritance step. HGT may violate compatibility with a purely reproductive pedigree; equality of owners and multi-generation steps must be treated explicitly. |
| Alexander 2026 background model | An infinite organism domain, finite children, strictly increasing birth times along the chosen parent edges, and finite earlier-time sets. A finite gARG does not supply these future conditions. |
| Alexander 2013 labelled population | In addition: finite roots, simple/functional edge labels and an incoming edge of every required role at every nonroot. Locus sets are not those labels, and unary suppression may change degree and immediate-parent structure. |
| Specieslike cluster | Weak connectedness inside the cluster, the infinite-ancestry property IAP, and convexity using ancestry in the ambient graph. Path soundness alone proves none of the three together. |
| Inspecies | Infinite ancestral closure and inclusion minimality among infinite ancestrally closed sets. This differs from maximal specieslike status. |
| Preservation through a quotient or simplification | Specify which paths lift, whether image fibres are finite, which vertices/intermediate ancestors remain, and which finite/cofinite sets and closure properties are preserved. Check each requested predicate separately. |

A full graph isomorphism, together with transported birth dates and role
labels, is a sufficient mathematical preservation condition for these
definitions. The existing genome-owner projection is generally many-to-one
and is **not** such an isomorphism. Even finite fibres by themselves do not
provide ancestry reflection or all the necessary path-lifting conditions.

## “Self-similar” is not an established bridge claim

The inspected paper does not assert that gARGs or Alexander's graphs are
self-similar. It describes shared node identities and edges across local
trees, equivalent encodings at a specified level of information, and
simplifications that discard some information. These are precise and useful
relationships; none says that a graph is isomorphic to a proper rescaled
copy of itself.

The repository separately proves dyadic Thue–Morse identities and exact
recurrences for one constructed graph's matching heights. Those identities
do not establish universal graph self-similarity. For example, doubling
vertices turns an allowed advance of two in P_s into an advance of four,
which is not an edge of that graph. This observation about the definition
is not a newly checked non-isomorphism theorem.

A future self-similarity claim must name the object, map, scale and invariant:
literal graph isomorphism, a quotient retaining selected observations, or
equality of probability laws after rescaling. No one of these should be
substituted for another without a proof.

## Coverage milestones and publication claims

| Order | Concrete deliverable | Completion test |
|---|---|---|
| 1 | Finite gARG foundation and sample-visible ancestry resolution | Individual checks passed for the interval DAG, local-parent representation, sample ancestry preservation, idempotence, nested/union laws and exact relation reconstruction criterion with counterexample. Executable sample-array extraction remains distinct. |
| 2 | Information retained by local-tree representations | Parent-relation representation, sample-support reconstruction criterion, concrete interval-gARG collision, local-arity bounds and backward traversal bound are checked; full serialization remains distinct. |
| 3 | Finite-record / infinite-population boundary | Ordered-prefix contrasting completions are checked. WongAlexander.actual_garg_opposite_infinite_completions is individually checked, deriving the numbering and including literal real birthdates. Neither result asserts a diploid bound or biological inference. |
| 4 | Concrete pedigree adapter | One specified cellular or organismal construction that supplies owner compatibility; keep genomic intervals separate from reproductive-role labels. |
| 5 | Selected simplification rewrites | Retained-node contraction and its composition with sample resolution are checked. Automatic finite-interval output for fixed node retention is now proved; individual software rewrite algorithms remain separate. |
| 6 | Larger paper coverage | Event/gARG round trips, arbitrary interval coordinates, executable traversal/serialization, probability and complexity theorems each receive separate models and receipts. Empirical claims receive reproduction evidence, not a Lean label. |

Milestones are reviewable stopping points, not permission gates. Work can
proceed under the user's existing authorization. Pending propositions must
retain that status until source fidelity, actual proof compilation and axiom
checks are recorded.

The [delivery map](../DELIVERY-MAP.md) now leads with this Wong–Alexander
connection in the explanatory packet and email. The quantitative Thue–Morse
result remains a separate VibeMathed submission candidate with its own prior
question. A faithful formalization of an established Wong statement is a
valuable contribution, but should not be advertised as a newly solved
previously open problem. No email, submission or repository publication is
performed by this source audit.


## Integrated source contracts

The [readable outline](../WONG-ALEXANDER-OUTLINE.md) and
[JSON connection map](../research/wong/connection-map.json) name each input,
transformation, hypothesis, output, preserved fact and information-loss boundary.
They supersede any earlier planning-only wording in the proof-contract section.
Final verification is the imported endpoint/source inventory in the core and
Mathlib receipts, not a claim that every empirical statement in this paper is a theorem.

## Follow-up closure

WongBreakpointCells, WongIntervalNormalization and WongSimplification close the supplied-partition and finite-output gaps for the specified sample restriction and fixed-node contraction. Each returned record has nonempty disjoint proper intervals; there is one record per ordered endpoint pair. Retained-to-sample ancestry is exact. Local uniqueness is inherited, and retaining every sample guarantees output sample support. Output breakpoints are a subset of input breakpoints. This does not impose a minimal segmentation or identify a complete software algorithm.

WongDiamond proves cutoff information loss even when all original edge-position incidences are sample-supported. FiniteGenomeIdentifiability explicitly rules out a universally correct whole-specieslike verdict over the topology-compatible completion class. Read the current aggregate source inventories and publication commit for the verification boundary.
