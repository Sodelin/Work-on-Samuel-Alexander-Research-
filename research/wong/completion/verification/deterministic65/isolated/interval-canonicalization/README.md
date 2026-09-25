# Canonical genomic interval records

## Source and purpose

Yan Wong et al. (2024), *A general and efficient representation of ancestral recombination graphs*, GENETICS 228(1), iyae100. [Primary article](https://doi.org/10.1093/genetics/iyae100), Appendix E, printed pp. 14–15: reconstructing genomic parent–child records by combining the local relations over their coordinate intervals.

The paper represents an edge annotation as a set of genomic positions. Different subdivisions of that set are mathematically equivalent. This module supplies a canonical **finite half-open interval representation** of those annotations: merge adjacent pieces for each fixed ordered parent–child pair until only strictly separated maximal pieces remain.

This is a representation theorem for the paper's known reconstruction argument, not a new result about inferring an ARG from observed sequences. The input local relations retain persistent node IDs and every node on each recorded inheritance path. Removed node identity, omitted event metadata, or unobserved branches cannot be recovered by interval merging.

For reconstruction from sample-traced local trees, equality with the entire original GARG additionally needs the existing sample-support condition: every original coordinate edge must lie on ancestry of a chosen sample. Without it, the reconstruction equals the sample-extracted relation. The general adapter represents exactly its supplied relation; `canonicalize` uses the full input `AtLocus` relation directly. It does not silently equate full local edges with sample-traced local trees.

## Exact mathematical contract

Let the coordinate domain be any linearly ordered type. Each supplied interval is proper and half-open:

$$
I=[\ell_I,r_I), \qquad \ell_I<r_I.
$$

The executable list operation merges a pair exactly when $r_I=\ell_J$. Its membership identity is

$$
[\ell_I,r_I)\cup[r_I,r_J)=[\ell_I,r_J).
$$

For an input list ordered with $r_I\leq\ell_J$ for every earlier/later pair, the output satisfies the strict condition $r_I<\ell_J$. This says that remaining intervals are both nonoverlapping and nonadjacent.

The selected proof endpoints establish:

1. **Semantic preservation:** every coordinate belongs to the output union if and only if it belongs to the input union.
2. **Endpoint reuse:** each output lower endpoint is an input lower endpoint, and each output upper endpoint is an input upper endpoint.
3. **Strict separation:** ordered disjoint inputs normalize to a list with a genuine coordinate endpoint gap between any two pieces.
4. **Fixed points and idempotence:** already separated lists remain exactly unchanged; a second normalization makes no change.
5. **Semantic uniqueness:** any two proper, sorted, strictly separated lists with identical membership at every coordinate are equal as lists. No density assumption is used; the excluded right endpoint itself witnesses any purported extension.
6. **Actual graph output:** the finite-cell adapter emits an actual GARG, with one nonempty record per active ordered parent–child pair, merged interval annotations, the same sample IDs, and exactly the same `AtLocus` relation.
7. **No new breakpoints:** when the adapter uses the existing automatic breakpoint cells, its output endpoint set is a subset of the original graph's endpoints.
8. **Full graph canonicality:** graphs with the same samples and `AtLocus` semantics have exactly equal canonical outputs; canonical graph reconstruction is idempotent.

The Lean check passed for all **31 selected endpoints**, including a kernel-evaluated finite example. The separate `#eval` printed `[(0, 3), (5, 6)]` after collapsing three touching intervals while retaining the gap before the fourth. Every selected axiom report is present; each uses only `propext`, `Quot.sound`, and/or `Classical.choice`. No placeholder or extra axiom occurs in the checked source.

**Proof status: PASS.** Lean 4.33.1 compiled the final LF source with exit code 0 on 2026-09-25. The measured final check took 14.096 seconds. There is one harmless linter warning: a section-level `Fintype Node` instance is unused by the interval-separation lemma. It does not affect the theorem or its axiom report. See `verification.json` for the exact source and validation hashes and `validation.txt` for the complete final compiler output.

## Computability boundary

`join`, `prepend`, and `mergeAdjacent` are ordinary Lean definitions, outside a `noncomputable` section. They implement a finite right-to-left list merge using the coordinate order's equality decision. They do not select a result using an existence theorem.

The general GARG envelope is explicitly **noncomputable**. Its abstract finite-set enumeration and arbitrary coordinate-activity predicates use classical decisions, as do the existing breakpoint and cell-presentation interfaces. Once a finite ordered cell list is supplied to the merge routine, the merge is executable. This module does not claim a byte-level serialization format, tskit import/export compatibility, a parser, or an end-to-end executable arbitrary-GARG exporter.

The graph stores interval regions as finite sets; the companion `serializedRegions` function supplies the unique ordered list for each parent–child pair. Thus graph equality and ordered interval-list equality are both available at their respective interfaces.

## Boundaries and examples

- **Gaps:** `[0,1)` and `[2,3)` remain separate. No gap is filled.
- **Touching pieces:** `[0,1)`, `[1,2)`, and `[2,3)` become `[0,3)`.
- **Empty relation:** the canonical list is empty and no parent–child record is emitted.
- **Distinct endpoint pairs:** merging is performed separately for each ordered parent–child pair. A parent change is never merged away.
- **Multiple or absent roots:** the algorithm does not assume a single local root or single parent; these properties are inherited when present because `AtLocus` is unchanged.
- **Original empty annotations:** topology-only records with no coordinate activity are omitted. Output topology equals the union of original local edge relations; equality with raw input topology requires the original records to have nonempty annotations.
- **Node identity:** node IDs and samples remain available. Isolated IDs are preserved in the fixed node type.
- **Maximality scope:** maximality is with respect to the represented coordinate set for that endpoint pair, not genomic inference or maximal biological ancestry.

## Files and review

- `WongIntervalCanonicalization.lean`: executable core and mathematical GARG adapter.
- `Check.ps1`: isolated compiler invocation using pinned existing caches.
- `selected-endpoints.json`: the 31 names required by the verification gate.
- `validation.txt`: the complete final compiler output.
- `final-run.json`: measured exit status and parsed actual axiom reports.
- `verification.json`: public-safe source/log hashes, toolchain pins, and scope boundaries.
- `CHECKPOINT.json`: completed checkpoint, retaining the earlier uncompiled checkpoint as history.

No shared Lean cache, previously completed proof module, public repository, or source PDF is modified by this lane.
