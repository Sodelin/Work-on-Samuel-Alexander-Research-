# Completing the Wong 2024 formalization

**Current status: partial paper coverage, with a checked new representation batch.**
The source is Yan Wong et al., *A general and efficient representation of ancestral
recombination graphs*, Genetics 228, iyae100 (2024),
[DOI](https://doi.org/10.1093/genetics/iyae100).

## Read in this order

1. [Claim-by-claim coverage](COVERAGE.md): 52 claim families across the main text and Appendices A–I.
2. [Executable sample tracing](../../../notes/WONG-SAMPLE-TRACING.md): actual interval records to persistent parent arrays.
3. [Normalized event decoding](../../../notes/WONG-EVENT-DECODING.md): full parent specifications and strict classical degree conventions.
4. [Coordinate-dependent simplification](../../../notes/WONG-LOCAL-SIMPLIFICATION.md): an actual finite interval output preserving specified ancestry.
5. [Rate-normalization audit](INITIAL-RATE-AUDIT.md): a written probability derivation and an unresolved source-interpretation issue.

Six integrated modules add 58 selected endpoints to the real project, whose
fresh local audit now checks 209. These are theorem-audit counts, not counts of
paper claims or novel discoveries. The source and exact endpoint inventory is
recorded in [the integration manifest](integration-manifest.json) and
[the aggregate receipt](../../../verification/real-audit.json).

## What remains

The coverage ledger retains explicit obligations for the actual stochastic
processes, termination and expected event costs, Big/Little ARG relationships,
fully coalesced material above local MRCAs, representation normalization and
other cited mathematical claims. Empirical comparisons and software timings
require reproduction evidence of their own. No full-paper completion is claimed.

The [memoized extractor](../../../notes/WONG-MEMOIZED-TRACING.md) and
[timed-history collision](../../../notes/WONG-TIMED-HISTORY.md) are included
in this fresh aggregate audit. Further results will update the ledger with their
own source hashes and verification records.

## Source fidelity

The authoritative Europe PMC article XML was preserved before parsing. Its
SHA-256, source URL and acquisition limits appear in [source-manifest.json](source-manifest.json).
The source XML retains MathML; the publisher PDF has an extra repository cover.
PDF visual inspection remains incomplete because the screenshot tool did not
return usable images. This limitation does not erase the exact MathML evidence
for the rate formulas, but it prevents a claim of completed visual verification.

The existing [Wong–Alexander bridge note](../../../notes/WONG-ALEXANDER-BRIDGE-STATUS.md)
explains the separate finite-record/infinite-population issue. The new
[feedback/speciation package](../../feedback-speciation/README.md) supplies
conditional pedigree and dynamical-model results, with its biological premises
and unverified extensions stated separately.

This is AI-assisted, internally reviewed work. Attribution, formal correctness,
source fidelity, empirical validity and novelty are distinct questions.
