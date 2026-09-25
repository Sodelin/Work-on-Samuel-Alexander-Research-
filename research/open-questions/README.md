# Open questions and genomic identifiability

This is the 25 September 2026 research notebook for three directions explicitly raised by Samuel Allen Alexander and a related genomic-identification question. **Written proofs and checked Lean statements have different verification status.** Most Lean files here are isolated research artifacts: their local checks are recorded separately from the main aggregate audit. The finite-completion obstruction is also integrated byte-for-byte as `real/FiniteGenomeIdentifiability.lean`, with its three endpoints included in the current Mathlib audit. Hosted CI does not automatically compile the other isolated artifacts.

## Readable map

| Question | Current result | Checked scope and remaining work |
|---|---|---|
| Can genomic data determine species? | [An exact information criterion, an ancestry-completion obstruction, and a known conditional positive example](genomic-identifiability/README.md) | Three local Lean endpoints establish the completion obstruction; the prescribed three-taxon law is also locally Lean checked. Neither is universal biological species delimitation. |
| Ordinal characterization of sequence realization | [Reachable-state ranks and the matching-tree ordinal dichotomy](ordinal/ORDINAL-CHARACTERIZATION.md) | Complete natural-rank characterization and least-rank construction for every `BinaryNatPopulation` are locally Lean checked. The full matching-tree ordinal and Schmidt-rank statements remain written-only. |
| Universal avoiding populations | [A language-preserving blow-up defeats every countable family of locally finite embedding hosts](embedding/UNIVERSAL-AVOIDER-NONEXISTENCE.md) | Complete written argument in the stated injective embedding category; no full Lean proof yet. Classical locally finite graph obstructions must receive prior-art attribution. Unbounded-stretch embeddings and uniformly capped subclasses require separate treatment. |
| A replacement for common ancestry in maximal specieslike existence | [A bounded founding period permits constrained maximal extensions](species/FOUNDER-WINDOW-THEOREM.md) | Complete written proof candidate; seven supporting natural-date lemmas locally Lean checked. The full real-date compactness and Zorn argument, and biological plausibility of the replacement, remain separate work. |

The first two graph questions come from [Alexander (2013), Section 6](https://arxiv.org/html/1212.0186v2#S6). The specieslike direction comes from [Alexander (2026), Section 6](https://arxiv.org/html/2602.05274v1#S6). These are scoped responses to the source questions, not a declaration that every intended interpretation of the open problems is closed. The ordinary matching-tree ordinal rank collapses to the same value for all avoiders; a richer structural classification remains open.

## Verification and reproduction

- [Separate AI embedding review and finite-stretch extension](embedding/INDEPENDENT-CHECK.md), including classical prior art; this is not independent human expert review.
- [Packet manifest](manifest.json): exact SHA-256 values for this frozen artifact batch.
- [Ordinal verification history](ordinal/VERIFICATION.md) and [new necessity/equivalence receipt](ordinal/NECESSITY-FORMALIZATION.md).
- [Finite completion obstruction receipt](genomic-identifiability/verification.json).
- [Positive law example and scope](genomic-identifiability/positive/README.md), with [compiler output](genomic-identifiability/positive/validation.txt).
- [Supporting founder lemmas](species/FounderWindow.lean) and [verification receipt](species/VERIFICATION.md); these do not formalize the entire existence theorem.

The checked local environment used Lean 4.33.1 and the repository's cached dependencies. Core imports correspond to the published library at `bcef6da64672310b314f2bc17c96f9535fcaaf5b`; the real project pins Mathlib in its manifest. In a prepared repository checkout, compile the standalone Std files directly and use the appropriate project environment for files importing the core library or Mathlib. For example:

```powershell
lake env lean research/open-questions/ordinal/OrdinalCertificates.lean
lake env lean research/open-questions/ordinal/ReachableRankNecessity.lean
lake env lean research/open-questions/species/FounderWindow.lean
Set-Location real
lake env lean ../research/open-questions/genomic-identifiability/FiniteGenomeIdentifiability.lean
lake env lean ../research/open-questions/genomic-identifiability/positive/ThreeTaxonIdentifiability.lean
```

These commands require the imported project modules to have been built. The archived local receipts identify what was actually checked; a future integration into the exported library requires fresh endpoint and source-hash receipts. Only `propext`, `Classical.choice` and `Quot.sound` occur in the reported proof dependencies; individual files may use a subset.

All work is AI-assisted. The positive identification example formalizes an established result; the graph recovery obstruction is an elementary consequence of our completion theorem. The embedding argument uses a classical graph-growth diagonal. Candidate novelty concerns exact statements and adaptations, not claims that these general methods were invented here. Worldwide priority and independent expert review remain unconfirmed.

## Delivery state

The reviewed email has been sent. **Exact Thue–Morse matching heights in an avoiding population** was submitted to VibeMathed on 25 September 2026 and was observed under review in its [queue](https://vibemathed.com/queue). That submission and the email refer to the earlier immutable snapshot `19544a4d7608c8cc0d5a1205605c0f38631ca05f`. They do not certify this later research notebook. No duplicate outreach accompanies this batch.
