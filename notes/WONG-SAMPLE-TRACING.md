# Executable and memoized extraction from actual interval records

Source: Wong et al. (2024), Appendix E, journal pp. 14–15. [DOI](https://doi.org/10.1093/genetics/iyae100); [primary full text](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/#app5). This is an attributed verification of the algorithmic model, with no novelty or external-software certification claim.

## What is checked

[WongSampleTracing](../real/WongSampleTracing.lean) gives a reference rootward traversal. [WongRecordTracing](../real/WongRecordTracing.lean) obtains parents by scanning actual finite interval records. [WongMemoizedTracing](../real/WongMemoizedTracing.lean) implements the shared cache and visited-entry early stop described in the paper.

For each sample, the memoized traversal stops at an already nonempty parent entry. Otherwise it looks up the parent, stops if none is found, or writes that parent and continues rootward. A proved cache-closure invariant justifies early stopping even though each entry is written before its ancestor is processed.

`memoExtract_eq_reference` proves the same result as repeated reference tracing. `records_to_memoized_sample_array` connects the algorithm directly to actual gARG interval records. The graph must be finite and acyclic with at most one parent per child at the chosen coordinate; record and sample lists must enumerate the corresponding sets exactly. Lists may be reordered or contain duplicates. Fuel equal to the node count suffices; decreasing ancestor count is used only in the proof.

The parent function retains original node IDs and unary ancestors. Each entry is the unique parent in the sample-supported local relation, or `none`. Root entries and unvisited entries both have `none`, so visiting a root again can repeat its lookup. No extra root-visited flag is assumed.

`memoized_records_round_trip_iff` proves that arrays at all coordinates recover all original indexed edges exactly iff every edge is sample-supported. This is equality of edge-position relations, not a canonical interval serializer or byte-format round trip.

## Exact abstract operation counts

The instrumented run counts successful nonempty cache writes, calls to the supplied parent lookup, and cache-entry checks. It proves:

```text
writes <= number of nodes
checks <= writes + number of listed samples
lookups <= writes + number of listed samples
```

`run_write_accounting` proves that the final number of filled entries equals the initial filled count plus writes. Thus a successful write fills a previously empty entry. A terminal cache check or root lookup is allowed for each sample, accounting for duplicates and repeated roots. Zero fuel performs none of these counted operations.

These cost inequalities themselves do not require acyclicity or sufficient fuel; extraction correctness does. **The bounds are abstract operation counts.** A parent lookup may scan many records, and a function-based cache may traverse accumulated updates. No constant-time lookup/update, record-comparison bound, allocation bound, CPU runtime or tskit performance claim is asserted.

## Concrete kernel checks

Closed `by decide` examples verify retained unary ancestry, exclusion of an unsupported branch and shared-path memoization. One shared-path example performs 3 writes, 4 lookups and 5 cache checks. Two repetitions of a root perform 0 writes, 2 lookups and 2 checks. These are correctness examples rather than benchmarks; no `native_decide` is used.

## Remaining boundaries

Sample-support restriction traces to graph roots. Removing fully coalesced material above a local MRCA remains a separate semantic operation. Multiple local roots give a forest; a connected tree needs an extra premise.

Canonical finite interval serialization, across-coordinate incremental update algorithms, machine-array costs, external file parsing, verification of tskit binaries and DNA-based inference of the input graph are separate claims.

## Verification

These three tracing/lookup modules contribute **21 selected endpoints** to the fresh **209-endpoint Mathlib aggregate**, checked on **25 September 2026 at 13:26:46 UTC**. Exact current hashes and standard-axiom reports are in [verification/real-audit.json](../verification/real-audit.json). The full six-module Wong completion batch contributes 58 new endpoints.

Reproduce with `python checks/audit_lean.py --real` after pinned dependency setup. The [PR checks](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/pull/6/checks) record hosted status separately for each exact publication commit.

