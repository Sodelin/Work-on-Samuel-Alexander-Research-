# Deterministic source correspondence and claim boundaries

This lead review compares the actual three module sources with the pinned
primary XML and the public 209-endpoint coverage ledger. The independent Sol2
review is separate. None of the 65 selected declarations in the three source files has
been changed during integration.

Primary source: Yan Wong et al. (2024), *A general and efficient representation
of ancestral recombination graphs*, DOI
[10.1093/genetics/iyae100](https://doi.org/10.1093/genetics/iyae100), XML
`PMC11373519-fullText.xml`, SHA-256
`2b77c349f39d2885b3e36d3bcab639a7ef3b9c6217263031aa4bc8f1c2a0d05e`.

| Source locator | Actual formal contract | Relationship and limitation |
|---|---|---|
| Main text `iyae100-s3`, Figure 3 and following discussion; printed p. 4 | `TruncatedAt = ExtractedAt` together with failure of `Common` at the child; actual `truncate G` and `finite_mrca_truncation` | Attributed deterministic formalization of removing entirely coalesced local history. This intentionally deletes some sample-supported ancestry. |
| Appendix B `app2`, paragraph 4; printed pp. 12–13 | `Common` is reflexive local ancestry of every designated sample; existence of an `IsMRCA` is proved with nonempty samples, unique local parenthood and an existing common ancestor | Gives an exact path-based stopping condition. It does not prove that a stochastic segment count equals the size of a disjoint descendant-sample set. Lineage merge/retirement transitions remain open. |
| Appendix E `app5`, paragraphs 2–3; printed pp. 14–15 | `CellPresentation.canonicalGARG_at`, `canonicalize_at`, `serialized_semantic_unique` and `canonicalize_semantic_unique` | Representation infrastructure for combining indexed local parent-child incidence into canonical finite interval annotations. Canonical storage is an explicit refinement of the source's interval-set representation. |
| Appendix E `app5`, paragraphs 4–7 | Existing sample-array iff theorem plus full-`AtLocus` input to canonicalization | Persistent IDs and unary paths are retained when supplied. Sample-traced arrays recover every original local edge only if `SampleSupported` holds; unsupported branches are invisible. No recovery of omitted event metadata or inference from sequences is established. |
| Appendix G `app7`, paragraphs 6–7; printed pp. 16–17 | `KeepSamplesAndBranching`, `retained_nonsample_branches`, `NoNonsampleUnary`, `finite_local_normal_form` | The final coordinate-dependent bypass rule is formalized. Local unique parents prevent two retained branches from rejoining. Samples stay protected, including sampled ancestors; unused catalogue IDs may be isolated. |
| Composition of Figure 3 stopping with Appendix G bypass | `finite_resolved_normal_form` and `canonical_resolved_normal_form` | Source-motivated deterministic composition returning an actual finite interval gARG. This is not a claim that every intermediate Figure 3/5 stage or the literal figures has been reconstructed. |
| Canonical interval records | `mergeAdjacent`, separation/uniqueness lemmas, `canonicalize_idempotent` | Formalization infrastructure, not asserted new mathematics. Only the list merge is executable; graph preparation remains noncomputable. The fixed point concerns storage, not a second full simplification pass. |

## What was checked

The declaration inventory has exactly 24 MRCA, 31 interval and 10 normal-form
endpoints, with no duplicate selected names. The source hashes match the
transferred final receipts and immutable input manifest. The 209 old endpoint
names are retained unchanged and in their original order after new imports;
65 names are appended, giving 274. The original 52 claim IDs, source URLs,
page locators and historical contracts are preserved in the new ledger.

The independent finite controls deliberately defeat stronger claims: ordinary
support filtering equals MRCA truncation; all ancestry survives truncation;
a common ancestor always exists; local multiple parents still guarantee a
latest MRCA; sample arrays see unrelated nonsample branches; every retained
catalogue node must branch; and arbitrary interval gaps/overlaps/ordering may
be ignored. Storage idempotence versus whole-pipeline idempotence is a theorem
scope distinction, not a tested counterexample to full idempotence.

## Evidence distinctions

- Axiom audit: selected declarations checked against the pinned Lean/Mathlib
  imports, with exact source hashes. The staged combined audit freshly
  rebuilds every local imported module.
- Source review: the manual comparisons above and Sol2's bounded adversarial
  review. Kernel acceptance alone would not establish this correspondence.
- Finite controls: independent small Python models and the existing Lean
  interval example. They illustrate assumptions; they are not general proofs.
- Hosted integration: a separate check on the exact commit published by the
  sole programme auditor. A local receipt cannot establish hosted status.

The source ledger's existing statement about unavailable visual PDF review is
preserved. This cycle reads XML text/structure and actual Lean statements; it
does not claim a new visual inspection of all paper figures or formulas.

## Remaining scope

The current additions close scoped deterministic M07, G05 and G06 contracts.
E03 stays partial because a full executable exporter is not proved. B03's
stochastic count/partition/overlay invariant is not closed by a deterministic
path test. The following also remain outside this packet: nonexplosion and
holding times; named path-law absorption beyond the separate count-chain work;
spatial Big/Little projection or coupling; expected-event and machine-runtime
costs; concrete parser/serializer and tskit conformance; the global Figure 5c
eligibility stage; and empirical/source-stated research questions elsewhere
in Appendices A–I.