# Local genetic MRCA truncation of a finite interval gARG

**Status: locally Lean-checked.** The isolated Lean 4.33.1 check passed all 24 selected endpoints with zero warnings and only the standard axioms propext, Classical.choice, and Quot.sound. No sorryAx occurred. Public integration and CI are separate checks.

## Source obligation

Wong et al. (2024), *A general and efficient representation of ancestral recombination graphs*, [DOI](https://doi.org/10.1093/genetics/iyae100), [primary PDF](https://www.pure.ed.ac.uk/ws/portalfiles/portal/458588307/iyae100.pdf).

The Fig. 3 discussion on printed p. 4 removes the grand MRCA when different genomic segments have already coalesced at younger local ancestors. Appendix B, printed p. 13, stops tracking a segment once its ancestral sample count reaches the total number of samples. This operation removes fully coalesced material, including some material that is still ancestral to every sample.

The prior `ExtractedAt` operation kept an edge whenever its child reached **some** sample at that locus. It therefore retained ancestry above a local MRCA. This module supplies a distinct stopping operation. All common ancestry here is **genetic ancestry at a fixed genomic coordinate**, not organismal genealogical common ancestry.

This is a deterministic finite-graph formalization of that source operation. It does not construct the Little ARG stochastic process or verify a particular software implementation.

## Exact stopping rule

Write $R_x(p,c)$ for the gARG's inheritance edge at position $x$, directed ancestor to descendant. Define reflexive local ancestry by

$$
A_x(a,b)\iff a=b\ \lor\ \operatorname{Reach}(R_x,a,b).
$$

Reflexivity matters when a designated sample is itself ancestral or the sample set has one member. Let $S$ be the designated sample set and define

$$
C_x(c)\iff \forall s\in S,\ A_x(c,s).
$$

The new edge relation is

$$
T_x(p,c)\iff
R_x(p,c)\ \land\
(\exists s\in S,\ A_x(c,s))\ \land\
\neg C_x(c).
$$

Thus an edge is retained only while its child's material is ancestral to at least one sample and has not yet coalesced across **all** samples. An edge into a common ancestor is removed. Under local single parenthood, sample-supported edges whose parent is at or below the MRCA remain.

`Common`, `Anc`, `IsMRCA` and `TruncatedAt` expose these definitions directly. There is no assumed sample-count annotation and no numerical count that could disagree with the path relation.

## Existence and uniqueness of the local MRCA

The existence theorem explicitly assumes:

- The input finite interval gARG is acyclic, as required by its type.
- The designated sample set is nonempty.
- At the selected locus, every child has at most one parent (`UniqueParentAt`).
- At least one node is a reflexive common ancestor of all designated samples.

Under these conditions, the theorem constructs a unique node $m$ satisfying

$$
C_x(m)\quad\text{and}\quad
\forall a,\ C_x(a)\Longrightarrow A_x(a,m).
$$

The proof maximizes the input gARG's derived topological code over its finite common-ancestor set. Local single parenthood makes two ancestors of a shared sample comparable. A strictly later common ancestor would violate maximality. The result concerns an order-defined MRCA; no arbitrary dates or tie-breaking among incomparable candidates are supplied.

For this $m$,

$$
C_x(c)\iff A_x(c,m).
$$

Hence the stopping rule deletes the incoming edge into $m$ and all supported edges with child at or above $m$. Under local single parenthood it equivalently retains exactly the supported edges whose **parent** lies at or below $m$:

$$
T_x(p,c)\iff G.\mathrm{ExtractedAt}(x,p,c)\land A_x(m,p).
$$

The phrase “at or below” includes $m$ itself. This retains paths starting at the MRCA and ending at its samples.

## Preserved information

The proof establishes:

- Strict sample-to-sample reachability is unchanged, including samples taken at ancestral nodes.
- Strict MRCA-to-sample reachability is unchanged.
- Every sample remains a reflexive descendant of the MRCA in the truncated relation.
- No edge enters the MRCA after truncation.
- Every retained edge remains ancestral to a sample **in the truncated graph itself**.
- Local single parenthood is inherited because the operation only removes edges.

It deliberately does **not** preserve paths from ancestors strictly above the MRCA into the samples. Those paths are exactly part of the fully coalesced history being removed.

`supported_but_removed` makes the difference from ordinary support filtering explicit: when the sample set is nonempty, any existing edge into a common ancestor is sample-supported but is excluded by this operation.

## An actual finite interval output

`truncatedPresentation` uses the automatically derived adjacent cells of the input annotation endpoints. Local edges, their finite paths, and the common-ancestor test are constant on each such cell. The retained relation therefore has a finite interval representation.

`truncate G` constructs an actual `GARG` with:

- Exactly the original finite node catalogue and sample IDs.
- Nonempty edge annotations.
- At most one interval record for each parent-child pair (`CanonicalRecords`).
- Precisely the local stopping relation $T_x$ at every coordinate.
- No coordinate endpoints absent from the input.
- Sample support in its own local relations.

Unused node IDs remain in the catalogue as isolated nodes. Therefore the theorem does not claim that the MRCA is the only graph-theoretic root in the entire catalogue. It is the top of the relevant sampled local ancestry. Record canonicality has the existing one-record-per-pair meaning; no byte serialization or maximal adjacent-interval merge is claimed.

The cell presentation and record construction are noncomputable mathematical functions. They certify representability and semantics, not tskit execution or runtime complexity.

## Boundary cases

| Case | Exact behavior |
|---|---|
| One designated sample $s$ | $s$ itself is the reflexive local MRCA, even without a parent edge. All local edges are removed, and the sample ID remains. |
| A designated sample is a common ancestor of all samples | That sampled node is the MRCA. Its paths to later samples remain. |
| No local common ancestor of all samples | The stopping rule agrees exactly with ordinary sample support extraction; it does not falsely declare complete coalescence. |
| Two distinct designated samples are local roots | No common ancestor can exist, providing an explicit multiple-root case. |
| Empty sample set | There are no retained edges. The existence/uniqueness theorem intentionally requires nonempty samples. |
| No unique local parenthood | The stopping relation and finite output still exist. The stated unique-MRCA existence theorem and below-MRCA edge characterization require their explicit uniqueness premise. |

Multiple isolated, unused catalogue nodes do not invalidate existence of a common ancestor for the actual samples. The multiple-root theorem concerns distinct **sampled** local roots.

## Selected theorem endpoints

The module registers 24 endpoints for the isolated axiom report:

- `exists_unique_mrca`, `mrca_unique`, `common_iff_ancestor_mrca`.
- `truncation_iff_cut_above`, `truncation_iff_below_mrca`, `supported_but_removed`.
- `sample_paths_preserved`, `mrca_sample_paths_preserved`, `mrca_reaches_every_sample`, `no_incoming_mrca`, `truncated_support`.
- `no_common_no_extra_truncation`, `ancestral_sample_is_mrca`, `singleton_sample_is_mrca`, `singleton_has_no_edges`, `empty_samples_no_edges`, `distinct_sample_roots_no_common`.
- `truncate_at_iff`, `truncate_unique_parent`, `truncate_sample_supported`, `truncate_breakpoints`, `truncate_sample_paths`, `truncate_mrca_paths`, `finite_mrca_truncation`.

The combined `finite_mrca_truncation` theorem provides the actual output, exact local semantics and preservation statements. MRCA existence is a separate theorem with its additional hypotheses visibly required.

## Scope

This is attributed formalization of a known stopping rule. It establishes no new result about biological species, no genealogy-to-genotype decoder, no mutation or likelihood equality, and no rate or complexity bound for stochastic ARG simulation. In particular, it must not be substituted for the unresolved stochastic obligations identified in the separate Appendix B rate audit.

## Local verification

Run [Check.ps1](Check.ps1) only when the shared compiler coordination slot is free. Its direct source import is `WongSimplification`; the earlier finite-gARG, breakpoint-cell and ancestry interfaces are already included through that module. Build output goes only to this lane's `.lake/build/lib/lean`. The exact successful output is preserved in [validation.txt](validation.txt); [verification.json](verification.json) records source, dependency and proof-artifact hashes. No existing source or shared cache was modified by this lane.
