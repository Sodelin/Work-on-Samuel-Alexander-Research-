# Memoized sample tracing (Wong Appendix E)

This isolated module verifies the caching and early-stop behavior of the sample-to-root traversal in Wong et al. (2024), *A general and efficient representation of ancestral recombination graphs*, DOI [10.1093/genetics/iyae100](https://doi.org/10.1093/genetics/iyae100), Appendix E, journal pp. 14–15. It is a formalization of the paper's algorithmic model, with an executable record scan supplied by `WongRecordTracing`; it is not certification of the tskit implementation.

## Executable algorithm

`memoExtract parent fuel samples` starts with every parent entry `none`. For each sample, `visit` checks the current cache entry. A nonempty entry stops the traversal. Otherwise it looks up the parent; a missing parent stops at a root, while a parent found at `p` is written into the cache before traversal continues from `p`. The updated cache is shared by subsequent sample traversals.

The output retains the original node identifier type. There is no node renumbering or unary-node suppression. Roots remain represented by `none`. That value also represents unvisited entries: a repeated root can require another parent lookup. No extra visited-root flag is silently introduced.

`run` and `visit` return the cache plus explicit abstract operation counts. The finite cache is represented by a function with equality-tested updates. This is an executable mathematical parent-array model; it does not assert the time or storage cost of a machine array.

## Correctness contract

The generic proof uses a natural-number rank that strictly decreases when moving from a child to its parent, and requires `rank s < fuel` for every sample `s`. Under these explicit assumptions:

- `visit_complete` proves the completed traversal has the correct parent entry at every node on that sample's ancestral trace.
- `visit_closed` proves cached nonempty entries have complete ancestry above them. This invariant justifies stopping at a cache hit even though each new entry is written before its parent is processed.
- `memoExtract_some_iff` characterizes an output edge exactly as an input parent edge whose child is equal to, or an ancestor of, a listed sample.
- `memoExtract_eq_reference` proves extensional equality with the slower reference traversal in `WongSampleTracing`, which repeats shared paths.

For an actual finite `GARG`, `actual_memoized_extraction` supplies the rank from the number of graph ancestors and proves that fuel equal to `Fintype.card Node` suffices. The graph's acyclicity proves strict rank decrease; the number of ancestors is strictly smaller than the number of nodes. No separate unproved termination premise is added to this endpoint.

`records_to_memoized_sample_array` composes the actual interval-record lookup with the cached traversal. It requires unique local parents at the coordinate and full record/sample list membership equivalences. Lists may contain duplicates and need not have a special order. Its conclusion is exactly:

```text
memoExtract (lookup records x) (card Node) samples c = some p
    iff G.ExtractedAt x p c.
```

`memoized_records_round_trip_iff` strengthens this to the original local edge relation at every coordinate if and only if `G.SampleSupported`. Without sample support, the traversal recovers the extracted relation; source edges outside sample ancestry are not recoverable from these sample traversals.

## Cost contract

The cost definitions count:

- `writes`: successful writes of a nonempty parent entry;
- `lookups`: calls to the supplied parent lookup, including an unsuccessful root lookup;
- `checks`: cache-entry inspections, including an inspection that stops on a cache hit.

The zero-fuel base case performs none of these counted operations. Correctness uses the sufficient-fuel hypotheses above. The following cost inequalities hold even without acyclicity or sufficient fuel:

```text
writes <= number of nodes
checks <= writes + number of listed samples
lookups <= writes + number of listed samples
```

`run_write_accounting` proves the stronger identity that final nonempty-entry count equals initial nonempty-entry count plus writes. Every write changes a previously empty entry, and subsequent visits preserve it. `run_cost_bounds` allows one terminal inspection/lookup per sample, so repeated root visits and duplicate samples are counted honestly.

These are abstract counts, not CPU/runtime bounds. A call to the imported record lookup can scan many records, and evaluating a functional cache can traverse updates. No constant-time lookup, constant-time update, allocation bound, tskit performance claim, or record-comparison bound is asserted.

## Kernel examples

The module includes three closed examples checked with `by decide`:

1. Two samples sharing an ancestor produce `[none, some 0, some 1, some 1]` on the four original node IDs.
2. The shared-path example performs 3 writes, 4 parent lookups, and 5 cache checks; its second traversal stops at the shared cached entry.
3. Two copies of a root sample perform 0 writes, 2 lookups, and 2 checks, illustrating the root/unvisited ambiguity of `none`.

## Source and verification receipt

The primary preserved source is `../source/PMC11373519-fullText.xml`, supplied by Europe PMC at [the full-text XML endpoint](https://www.ebi.ac.uk/europepmc/webservices/rest/PMC11373519/fullTextXML). Its SHA-256 is `2b77c349f39d2885b3e36d3bcab639a7ef3b9c6217263031aa4bc8f1c2a0d05e`. The traversal description is `/article/body[1]/sec[14]/p[2]`; subsequent Appendix E paragraphs discuss persistent IDs and unary nodes. The repository's publisher-version PDF is [Appendix E, physical page 15](https://www.pure.ed.ac.uk/ws/portalfiles/portal/458588307/iyae100.pdf#page=15), corresponding to journal page 14 because of the repository cover. The XML extraction is marked unverified against visible PDF pages; no local PDF bytes or PDF hash are claimed.

Run `Check.ps1` in this directory to compile against the existing Lean 4.33.1 and frozen owner/root dependency caches. It writes only this directory's `WongMemoizedTracing.olean`. `validation.txt` records the final compiler output; `verification.json` records the command, version, endpoint axiom reports, dependency hashes, and outcome. Ten selected proof endpoints are audited using `#print axioms`.

No code in the owner repository, other implementation lanes, or public services is modified by this isolated module. The work supplies a source-aligned mathematical verification, with no novelty claim and no biological-species conclusion.

## Integrated verification

This module is registered in the real-number project and RealAudit.lean.
The fresh aggregate passed 209 selected endpoints on 25 September 2026,
including the six new Wong modules (58 endpoints). Exact source hashes and
standard-axiom reports are in [the receipt](../verification/real-audit.json).
Reproduce with `python checks/audit_lean.py --real` after pinned dependency setup.
The [PR checks](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/pull/6/checks)
record the separate hosted result for each commit.
