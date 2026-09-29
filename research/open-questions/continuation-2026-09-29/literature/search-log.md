# Search and source-access log

Date: 2026-09-29. Start: 20:14:25 UTC. Final substantive metadata check: approximately 20:20 UTC. Mode: rapid evidence map/current public-state verification. Domain: infinite labelled directed graphs and mathematical genealogy. Concepts: Alexander populations, universal avoiding populations, injective subgraph embeddings, finite branching, local growth, well-founded ordinal certificates, Schmidt/Halin rank. No date cutoff; primarily English reading with bibliographic discovery of German Schmidt sources. Exclusions: biomedical entity/clinical databases as proof sources; secondary summaries as decisive mathematical evidence; unverified novelty claims.

The literature-evidence-router skill and its source-routing/evidence-ledger references were read. Parent agent applied the Life Science Research router; this lane followed domain rather than the word “biological.” Installed alphaXiv capabilities were discovered from the live tool inventory and successfully used. No library writes, account actions, installations, messages to researchers or publications were performed.

## Discovery queries

All web queries used the available web search interface without a date/domain restriction unless shown. The interface returned ranked combined samples for batches and did not expose a stable per-query total or pagination denominator; no completeness count is asserted.

| Pass | Exact queries or tool arguments | Observed yield and use |
|---|---|---|
| W1 | `Samuel Alexander biologically unavoidable sequences 2013 P31 universal ordinal`; `Lehner "A note on classes of subgraphs of locally finite graphs"`; `"de Bruijn" Rado universal graph locally finite`; `Cherlin Shelah math/0512218` | Located Alexander arXiv/journal copies, Lehner author PDF/arXiv and Cherlin–Shelah arXiv. De Bruijn query also returned unrelated de Bruijn-sequence pages; those were excluded. |
| A1 | alphaXiv discover: difficulty 6; keywords `Biologically Unavoidable Sequences`, `universal`, `locally finite`, `ordinal`; prioritize `historical`; question `What primary mathematical literature addresses Alexander's universal-avoider embedding and general ordinal-characterization questions for biologically unavoidable sequences?` | One displayed candidate: arXiv:1212.0186. The small result is a relevance sample, not a negative literature finding. |
| W2 | `"Biologically unavoidable" "ordinal"`; `"Biologically unavoidable" universal embedding`; `"rayless" "Schmidt" rank ordinal graphs`; `"Universal graphs and universal functions" Rado 1964` | Located Rado/EuDML/publisher metadata, accessible rank expositions and Bürger–Kurkofka. Full texts then checked independently where available. |
| W3 | `"Universal graphs and universal functions" pdf Rado de Bruijn`; `"Biologically unavoidable sequences" "classification" Alexander`; `"Biologically unavoidable sequences" "universal" -site:researchgate.net -site:philarchive.org`; `"Ein Ordnungsbegriff" Schmidt 1983` | Located current VibeMathed classification context and repeated primary records; no independently verified exact external response to both population questions. VibeMathed was not used as mathematical proof. |
| A2 | alphaXiv discover: difficulty 5; keywords `locally finite graphs`, `rayless graphs`, `ordinal rank`, `universal graphs`; prioritize `recency`; question `Which mathematical results connect ordinal ranks of rayless graphs and embedding universal locally finite graphs, especially for infinite forbidden paths?` | Tool succeeded but the combined display was truncated. No candidate identity or negative-result inference relies on its hidden portion; only independently retrieved primary records are cited. |
| W4 | `"A note on classes of subgraphs of locally finite graphs" correction erratum 10.1016`; `"Universal graphs with a forbidden subtree" 2007 DOI correction`; `"Biologically unavoidable sequences" erratum correction`; `"Twins of rayless graphs" journal DOI` | Recovered Cherlin–Shelah published PDF, Twins journal identity and Alexander journal record. No correction notice verified in this bounded pass. This is not an exhaustive integrity search. |

## Full-text and identity checks

- Alexander journal page: https://www.combinatorics.org/ojs/index.php/eljc/article/view/v20i1p31 — identity, DOI and publication date verified.
- Alexander journal PDF: https://www.combinatorics.org/ojs/index.php/eljc/article/download/v20i1p31/pdf/ — full extracted text, Definition 1 and Section 6 inspected; 13 pages.
- Alexander arXiv: https://arxiv.org/abs/1212.0186 and https://arxiv.org/pdf/1212.0186v2 — version and text inspected; 9 pages. Different numbering from journal.
- Lehner arXiv: https://arxiv.org/abs/2205.12824 — v1 posted 25 May 2022. AlphaXiv `get_paper_content` with `fullText: true` returned raw full text successfully.
- Lehner author manuscript: https://www.florian-lehner.net/pdf/universal-locally-finite.pdf — full extracted text inspected, especially Theorems 1.1/1.2/3.1, Corollary 3.6, bibliography. Author page https://www.florian-lehner.net/ verifies journal linkage.
- Lehner DOI: https://doi.org/10.1016/j.jctb.2023.02.001 — web open returned internal error. No full journal-version comparison claimed.
- Cherlin–Shelah arXiv: https://arxiv.org/abs/math/0512218 and https://arxiv.org/pdf/math/0512218 — introduction and theorem read. Printed regenerated PDF date is not publication date.
- Cherlin–Shelah published PDF: https://sites.math.rutgers.edu/~cherlin/Paper/2007ForbiddenTree.pdf — 41-page version of record successfully opened; p. 293 definitions and p. 295 Theorem 1 inspected. DOI 10.1016/j.jctb.2006.05.008 appears in the PDF.
- Rayless rank manuscript: https://www.uni-ulm.de/fileadmin/website_uni_ulm/mawi.inst.081/Henning/raylesstwins.pdf — full text opened. AlphaXiv `answer_pdf_queries` queried exact Definition 2 and Schmidt/Halin bibliography, successfully returning original page text. Source version says 28 September 2009.
- Twins journal: https://www.sciencedirect.com/science/article/pii/S0095895610000948 — journal identity/DOI metadata retrieved. Alternate published PDF https://math.ryerson.ca/~abonato/papers/raylesstwins.pdf was found in search but direct open failed; not needed for the inspected definition.
- Halin: https://link.springer.com/article/10.1007/BF02942564 — metadata and bibliography inspected; full article subscription-gated. No purchase/access bypass attempted.
- Rado EuDML: https://eudml.org/doc/207488 — metadata available through search; direct open returned 403.
- Rado publisher: https://www.impan.pl/get/doi/10.4064/aa-9-4-331-340 — web open failed; ordinary read-only HTTP retrieved publisher HTML and its displayed download link successfully. https://www.impan.pl/shop/publication/transaction/download/product/95477 then failed in web open. No original full text relied upon.
- Rado title-resolution fallback: alphaXiv `answer_pdf_queries` with paper `Universal graphs and universal functions, Richard Rado, Acta Arithmetica 9 (1964), 331–340` asked for the de Bruijn nonexistence theorem/proof and countable-family/bounded-stretch coverage. The tool returned **the wrong paper**, `1912.06770v2`, *Geometric random graphs on circles* (Angel–Spinka). The identity mismatch was detected immediately; all its content was excluded from evidence about Rado. No original Rado full-text claim was added.
- Bürger–Kurkofka: https://arxiv.org/abs/2006.01071 and https://arxiv.org/pdf/2006.01071 — v1/v2/v3 dates and relevant theorem/rank-definition text inspected.

## Current public research checks

Public API calls used `Accept: application/vnd.github+json` and a descriptive user-agent; no authentication secret was read or sent.

1. `https://api.github.com/repos/Sodelin/Work-on-Samuel-Alexander-Research-/pulls/6` — returned open/draft/unmerged, head `01db8c4cbb82000950ff7d3e7252b5438416c7c3`, base main `3bbd85d64e253ff797542aa3fe620b0de2fac54c`, update `2026-09-27T02:38:53Z`.
2. Recursive Git-tree endpoint for head and base: `/git/trees/{sha}?recursive=1` — both `truncated: false`; relevant directory entries 29 vs 0.
3. Immutable raw statement files under `https://raw.githubusercontent.com/Sodelin/Work-on-Samuel-Alexander-Research-/01db8c4cbb82000950ff7d3e7252b5438416c7c3/research/open-questions/` — `embedding/UNIVERSAL-AVOIDER-NONEXISTENCE.md` and `ordinal/ORDINAL-CHARACTERIZATION.md` inspected.
4. `https://api.github.com/repos/Sodelin/Work-on-Samuel-Alexander-Research-/actions/runs?head_sha=01db8c4cbb82000950ff7d3e7252b5438416c7c3&per_page=10` — total_count 0; no current-head successful-run claim.
5. `https://api.github.com/repos/Sodelin/Work-on-Samuel-Alexander-Research-/actions/runs/36127053780` — completed/success, head `8fd86430e78fed06fffe35df2fa85f28bdff48d9`, created `2026-09-25T11:00:38Z`, updated `2026-09-25T11:02:50Z`.
6. Recursive tree at `8fd8643` compared with current head — nine of nine embedding/ordinal `.lean` blobs identical. Exact hashes below.

| File under `research/open-questions/` | Git blob SHA at both commits |
|---|---|
| `embedding/GenericUniversalAvoiders.lean` | `64bc8ef2a28c7621a67327bc33cb5d5d58443340` |
| `ordinal/GenericCertificate.lean` | `ae6837b8addc241fa3f47adab21ffc8a602c61a5` |
| `ordinal/GenericOrdinalCertificate.lean` | `8c7a4d2c4e18f5f757c6ab1cd0b0ac665e62661e` |
| `ordinal/HistoryConverse.lean` | `2416baca006c479ecf172af89c0d93106b28155f` |
| `ordinal/HistoryPruning.lean` | `ce4e931254a98f5f3a1142de29fa259bb5cd43f9` |
| `ordinal/HistoryWellFounded.lean` | `63bbda1488aeb6c80aa474b68f7a7a469860d3d9` |
| `ordinal/OrdinalCertificates.lean` | `867dc062efaedcdf95fa241452265c3ccf8120cc` |
| `ordinal/OrdinalHistoryRank.lean` | `aad33da361604debef401b6a2ddf3efd45e41740` |
| `ordinal/ReachableRankNecessity.lean` | `ca2452f7e94c0946d939c69684682680ae59f509` |

## Local context and operational failures

Relevant local notes read: `QUESTION-LEDGER.md`, `PRIOR-WORK-AUDIT.md`, `BIOLOGICAL-MODEL-SCOPE.md`, `notes/OLDER-CONSTRUCTIONS-AND-RANK-AUDIT.md`, with targeted filename/citation searches. They were treated as previous research context, not proof that current public status matched them. No relevant match was found in the memory registry keyword search, so no memory-derived fact was used.

Initial sandbox shell helper failed with `helper_unknown_error: apply deny-read ACLs` when reading the skill. An escalated read-only command succeeded. No policy-rejected action or destructive workaround occurred. One accidental `web.click` passed an unresolved search-result reference and returned an invalid-arguments error; it supplied no evidence. Several large parallel outputs were truncated, so decisive claims were reacquired in targeted calls or discarded as evidence.

## Stopping boundary

Enough direct evidence was obtained to establish the exact source questions, current branch/file state, classical embedding convention, local-growth precedent and distinct rank definitions. No exhaustive citation-graph walk, MathSciNet/zbMATH review, Rado/Schmidt archive hunt, empirical biology expansion or external write was necessary for this bounded deliverable. Source-level Lean validation belongs to the other delegated lanes.
