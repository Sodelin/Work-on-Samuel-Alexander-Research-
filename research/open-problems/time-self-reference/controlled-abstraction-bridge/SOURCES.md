# Sources, correspondence and evidence boundaries

This inventory records what this cycle actually inspected. It does not inherit a claim to full reading from another task's notes. SHA-256 values, public repository locators, source identities and unavailable internal-intake labels are recorded in SOURCE-MANIFEST.json.

## Source question and motivation

| Source | Exact locator used | Supported use | Boundary |
|---|---|---|---|
| Abramsky, Banzhaf, Caves, Levin, Machado, Ofria, Stepney and White, Open questions about time and self-reference in living systems, Royal Society Open Science 13:261059 (2026) | DOI 10.1098/rsos.261059; published PDF p.11, section 4.2; page-linked extraction lines 642–657 | Q04's process/result-projection question | Our intervention-preserving quotient is a selected formal interpretation, not the entire source question |
| Same paper; canonical Q09 ledger | Published p.22, section 6.4.3; extraction lines 1296–1323; pinned Q09 ledger | Games in which decisions can merge or split decision makers | The new decision toy has fixed semantics and no game solution concept |
| Michael Levin, Biology, AI, and Diverse Intelligence | Supplied original transcript lines 313–351, timestamps 31:01–34:50 | Speaker report about memory/forgetting in mathematical molecular-network models | Does not state our three-bit cell model or its four interventions |
| Karl Friston, The Physics of Motivation | Supplied original transcript lines 392–414, timestamps 49:31–52:08 | Action selection can seek information about hidden states, parameters and model structure | Does not state our parity device or prove its empirical applicability |

Primary links: [paper DOI](https://doi.org/10.1098/rsos.261059), [Levin video](https://www.youtube.com/watch?v=Or_3tlEOLj4), [Friston video](https://www.youtube.com/watch?v=Fus2k7F5iN4). Video links and timestamps come from the supplied source metadata/text; no independent video viewing or transcript-fidelity certification occurred. The DOI landing page did not load in the web tool; the supplied published PDF's existing page-linked text is the version used. A search returned a 2025 preprint, which was not substituted for the published version.

Verified local source copies (not packaged): the published article PDF identified by DOI 10.1098/rsos.261059; the supplied Michael Levin transcript identified by video ID `Or_3tlEOLj4`; and the supplied Karl Friston transcript identified by video ID `Fus2k7F5iN4`. Exact byte lengths, SHA-256 hashes, line locators and public identifiers are recorded in SOURCE-MANIFEST.json.
Existing internal intake records read: its README, synthesis and handoff, source matrix, paper note, and selected L08 and Friston source-note content. These internal records are not included in this public packet; their available byte hashes are retained as descriptive provenance in SOURCE-MANIFEST.json. The present cycle checked the stated original transcript passages and selected paper extraction; it did not reread all ten transcripts or all 29 PDF pages.

## Exact reused formal sources

Repository: Sodelin/Work-on-Samuel-Alexander-Research-.
Pinned commit: 138dd529643ae5706a9df6a750bd6344ab967a8a.
Public prefix: research/open-problems/time-self-reference/.

| Source | Locator | Use |
|---|---|---|
| ExactAbstraction.lean | lines 14–15 | Definition of actionwise fibre compatibility |
| ExactAbstraction.lean | lines 19–33 | exact_factor_iff: existence iff compatibility under surjectivity |
| ExactAbstraction.lean | lines 36–42 | exact_factor_unique |
| ExactAbstraction.lean | lines 44–67 | Controlled trajectory definition and preservation under identical input sequence |
| MergeHistoryProjection.lean | lines 117–126 | Same current partition and different restored partitions |
| MergeHistoryProjection.lean | lines 128–162 | Incompatibility and impossibility of exact partition-only splitting |
| PUBLIC-VERIFICATION.json | modules, source hashes, axiom reports, timestamp | Prior proof-checker evidence for 16 selected endpoints |
| problem-ledger.json | Q04 and Q09 entries | Source correspondence, precise solved subproblems and remaining broader gaps |

[Q04 source](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/138dd529643ae5706a9df6a750bd6344ab967a8a/research/open-problems/time-self-reference/exact-abstraction/ExactAbstraction.lean#L14), [Q09 source](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/138dd529643ae5706a9df6a750bd6344ab967a8a/research/open-problems/time-self-reference/exact-abstraction/MergeHistoryProjection.lean#L117), [prior receipt](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/138dd529643ae5706a9df6a750bd6344ab967a8a/research/open-problems/time-self-reference/exact-abstraction/PUBLIC-VERIFICATION.json), [ledger](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/138dd529643ae5706a9df6a750bd6344ab967a8a/research/open-problems/time-self-reference/problem-ledger.json).

The GitHub tree page was unavailable to the web tool, and the ordinary local repository lacked this commit's tree. The two pinned Lean modules and their public verification receipt are included byte-for-byte at their canonical repository paths in this packet. Their hashes equal the source hashes in the pinned receipt. The problem ledger is linked at its immutable commit URL but its snapshot is not included:

- ExactAbstraction.lean: a5c8c5113532bfabb84e5259be91c551ab4210ce4301afc7a6fc233cab40c42e
- MergeHistoryProjection.lean: c040d1e74335ad2c86b050503df81b16eecce429ab8a063b6ea2f42af2971554

The receipt reports Lean 4.33.1, 16 selected endpoints, and no sorryAx. Standard listed axioms include Classical.choice, propext and Quot.sound. This is reused recorded evidence plus fresh byte comparison. This cycle did not rerun the compiler, reproduce hosted CI, or prove the new toy/minimality declarations in Lean.

## Direct prior-work comparison

Givan, Dean and Greig, Equivalence Notions and Model Minimization in Markov Decision Processes, Artificial Intelligence 147 (2003), 163–223. [Author-hosted 62-page manuscript](https://cs.brown.edu/people/tdean/publications/archive/GivanetalAIJ-03.pdf).

Inspected locations in that manuscript: section 2.2, printed pp.6–7; section 3.2/Theorems 1–2, printed pp.11–12; section 3.3/Theorem 7, printed pp.12–14. PDF physical pages agree with the printed manuscript numbering. These are manuscript page numbers, not journal page numbers.

The comparison is structural: their quotient states aggregate concrete states with actionwise compatible block transitions; their MDP result also preserves rewards. Our deterministic quotient is within that established reduction pattern. No reward function is part of our toys, so their optimal-policy conclusion is not imported. These definitions and theorem statements were inspected; a full proof-by-proof prior-art survey was not performed. Novelty is unestablished and not claimed.

## Existing stochastic result and review status

An existing synthesis in the internal Friston-Levin intake reports a controlled stochastic transport theorem, a written independent audit, finite checks, and approximate finite-horizon bounds. It is broader than the deterministic core used here. This cycle read that internal synthesis and retains its evidence label without claiming to have independently re-audited its full proof. It is not included here and is not offered as a public reproduction artifact.

The programme auditor reviewed and accepted the statement-only maps for bounded development, with explicit challenges about surjectivity, intervention meanings and the refinement order. This is not an independent final acceptance of the completed packet. FINITE-CHECKS.json is author-run evidence. Final adjudication and publication remain with the auditor.

Two later messages relayed external Stentor predictive-analysis results and a planarian source-selection caution. Those artifacts were not inspected or relied on in this cycle. They remain external, unreviewed empirical handoffs and are not evidence for this theorem or these toy equations.

