# Open questions and genomic identifiability

This is the 25 September 2026 research notebook for three directions explicitly raised by Samuel Allen Alexander and a related genomic-identification question. **The principal theorem chains now have complete local Lean checks at the scopes below.** Written extensions, historical receipts, integrated library checks, and the current publication gate remain separately identified.

For an accessible orientation, start with the [completion map](../../COMPLETION-MAP.md). This note records local completion before publication. The exact-commit hosted result is recorded in [PR #6 and its checks](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/pull/6/checks). Earlier successful runs certify their own snapshots.

## Readable map

| Question | Locally checked result | Exact scope and remaining work |
|---|---|---|
| Can genomic data determine species? | [An exact information criterion, an ancestry-completion obstruction, and a known conditional positive example](genomic-identifiability/README.md) | The obstruction concerns whole-population specieslikeness of topology-compatible infinite completions. The positive example assumes a prescribed exact three-taxon law. Neither is biological species delimitation from DNA. |
| Ordinal characterization of sequence realization | [Generic reachable-state certificates and checked matching-history ranks](ordinal/ORDINAL-CHARACTERIZATION.md) | Ordinal certificates cover arbitrary vertex/label types without finite branching. Natural certificates, leastness and attainment need finite per-label branching. Actual history root rank and first-limit pruning are checked for `BinaryNatPopulation`; Schmidt/kernel and the realizing fixed point remain written-only. |
| Universal avoiding populations | [A language-preserving blow-up defeats every countable family of locally finite embedding hosts](embedding/UNIVERSAL-AVOIDER-NONEXISTENCE.md) | Complete generic population construction with actual real dates, arbitrary vertex/label types, exact language, root equivalence, and injective edge or finite globally bounded-stretch obstruction. Arbitrarily unbounded stretch, ancestry-only embeddings, and fixed child caps are outside this result. |
| A replacement for common ancestry in maximal specieslike existence | [The complete real founder-window existence theorem](../../notes/REAL-FOUNDER-WINDOW-THEOREM.md) | For natural-number organism identifiers with actual real birthdates, a fixed nonnegative duration yields maximal connected, convex, IAP+REF window clusters through every organism. The genuine seed, directed-union argument, real duration, and constrained Zorn maximality are proved. Biological plausibility and novelty remain separate. |

The graph questions come from [Alexander (2013), Section 6](https://arxiv.org/html/1212.0186v2#S6); the specieslike direction comes from [Alexander (2026), Section 6](https://arxiv.org/html/2602.05274v1#S6). These are precise mathematical responses to the stated directions. The historical wording does not fix every intended embedding category or require a rank distinguishing different avoiders. The ordinary history-tree rank collapses to the same value for all avoiders, so a richer structural classification remains a separate question.

## Verification and reproduction

The integrated library has **405 core endpoints and 151 real/Mathlib endpoints**. The latter includes fifty new registered founder-proof endpoints and the three previously integrated finite-completion obstruction endpoints. Its source hashes and local checks are in the [core receipt](../../verification/formal-audit.json) and [real receipt](../../verification/real-audit.json).

The separate research-artifact audit **passed locally with 52 printed endpoints across 11 files**: 39 from the prior standalone inventory, three generic ordinal endpoints, and ten generic embedding endpoints. This inventory is distinct from the integrated library totals. The combined local pass was recorded at 10:56:58 UTC on 25 September 2026. The exact-commit hosted result is recorded separately in PR #6 and its checks.

Relevant evidence:

- [Actual binary history rank and pruning receipt](ordinal/COMPLETION-RECEIPT.md): eleven new endpoints and six unchanged prerequisite endpoints.
- [Generic natural-certificate theorem](ordinal/GENERIC-CERTIFICATE.md) and [source](ordinal/GenericCertificate.lean): eight endpoints, arbitrary types under finite per-label branching.
- [Generic ordinal-certificate source](ordinal/GenericOrdinalCertificate.lean): three endpoints, arbitrary types without finite branching.
- [Earlier ordinal verification history](ordinal/VERIFICATION.md) and [necessity receipt](ordinal/NECESSITY-FORMALIZATION.md): preserved historical evidence, superseded only where a later proof expands coverage.
- [Generic embedding theorem](embedding/GenericUniversalAvoiders.lean) and [separate AI review and prior art](embedding/INDEPENDENT-CHECK.md). The full generic Lean theorem closes the construction and diagonal chain; the earlier review remains a record of the written proof review, not human endorsement.
- [Complete founder theorem and source map](../../notes/REAL-FOUNDER-WINDOW-THEOREM.md). The [initial founder note](species/FOUNDER-WINDOW-THEOREM.md), [supporting file](species/FounderWindow.lean), and [old receipt](species/VERIFICATION.md) retain their narrower historical scope.
- [Finite completion obstruction receipt](genomic-identifiability/verification.json), plus the integrated `real/FiniteGenomeIdentifiability.lean` audit.
- [Positive law example and scope](genomic-identifiability/positive/README.md), with [compiler output](genomic-identifiability/positive/validation.txt).
- [Notebook manifest](manifest.json): exact hashes for the publication's research-artifact snapshot.

Lean is pinned to 4.33.1 and Mathlib to the repository's recorded revision. The ordinary workflow builds project imports and the standalone dependencies before checking the files and printed axiom reports. In particular, `GenericCertificate.lean` must produce an importable module before `GenericOrdinalCertificate.lean`; the actual history modules use the order listed in their completion receipt. The source files and receipts record the local commands. Only `propext`, `Classical.choice`, and `Quot.sound` occur in the reported proof dependencies, or a subset of these.

## What remains uncertain

- **Originality:** a bounded literature search does not establish worldwide priority. The positive law example is known; the ordinal proof uses classical well-founded ranks; the embedding obstruction uses a classical locally finite graph method. Candidate novelty concerns the exact statements and population adaptations.
- **Independent assessment:** separate AI reviews are not independent human expert review or Alexander's endorsement.
- **Biology:** the founder duration's empirical meaning, genome-to-organism modelling, and biological species identification require further justification. No general psychological theory follows from these proofs.
- **Further mathematical statements:** Schmidt rank/kernel, the realizing-population pruning fixed point, and the source-wide generic version of the explicit history-root calculation remain written-only. More embedding notions or a richer rank hierarchy require new specified theorems.

## Delivery state

The reviewed email has been sent. **Exact Thue–Morse matching heights in an avoiding population** was submitted to VibeMathed on 25 September 2026 and was observed under review in its [queue](https://vibemathed.com/queue). That submission and the email refer to the earlier immutable snapshot `19544a4d7608c8cc0d5a1205605c0f38631ca05f`. They do not certify this expanded notebook. No duplicate outreach accompanies this batch.
