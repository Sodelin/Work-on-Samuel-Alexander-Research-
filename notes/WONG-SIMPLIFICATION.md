# Automatically re-encoded finite gARG simplification

**Integrated aggregate check passed: 405 core endpoints and 101 mathlib endpoints.** The coordinator's serialized Lean checks passed for the automatic breakpoint-cell provider, the generic representation theorem, and the composition wrapper. The accepted sources are in `real/`.

`WongSimplification.automatic_reencoded_simplification` composes two constructions:

1. `WongBreakpointCells` derives adjacent proper half-open cells from the actual finite set of input annotation endpoints. Every coordinate supporting an input edge belongs to a cell, different cells are disjoint, and inheritance is constant on each cell.
2. `WongIntervalNormalization` groups the active cells of each parent–child pair into one finite record, proves the resulting graph is a DAG, and checks its full local edge semantics.

The resulting theorem takes only an actual finite `GARG G` and a fixed node-retention predicate `K`. It returns an actual finite `GARG H` with all of the following:

- The same sample set and finite node catalog.
- Nonempty annotations and at most one record per ordered parent–child pair.
- Exactly the relation obtained by sample-ancestry restriction followed by contraction through unretained internal nodes, at every coordinate and node pair.
- Exactly the original ancestry from a retained start to a retained sample, at each fixed coordinate.
- The unique-parent property wherever the original local relation has it.
- Sample support if every designated sample is retained.
- No new genomic breakpoints: `H.breakpoints` is a subset of `G.breakpoints`.

The single-parent result follows by comparing the final edges of two hidden paths into one vertex. A single-edge path and a longer path would make one retained start an unretained internal vertex, which is impossible. When both paths are longer, their final parents agree and the argument reduces to the prefixes. No global acyclicity premise is needed for this auxiliary uniqueness lemma, although both final gARGs independently have DAG proofs.

This closes the earlier missing *finite interval output* step for these specified operations. The output is a graph with actual proper disjoint interval records, not only a relation. Automatic cell generation removes the need for a caller to supply or assume a valid coordinate partition.

Several boundaries remain precise. The construction is noncomputable Lean mathematics using classical decidability, not a verified executable implementation. It does not merge adjacent intervals or produce a globally minimal interval segmentation; canonical records mean one row per parent–child pair. Unretained nodes remain as isolated identifiers in the original catalog. `K` is fixed across coordinates, so this result does not yet implement a different local retention rule in every genomic cell. Keeping all samples is sufficient for output sample support; it is not asserted necessary. In the separate diamond example, equal contracted relations can still yield differently segmented output records: `[0,cut)` and `[cut,3)` may preserve the old cut as redundant syntax. The relation-level information-loss theorem therefore does not assert equality of these automatically generated record objects. The diamond construction separately exhibits a common chosen full-span output; that is distinct from proving the automatic normalization function yields identical record objects. A further adjacent-cell coalescing proof would be needed for that stronger automatic storage claim. None of these operations reconstructs removed crossover identities or establishes correctness of tskit.

## Files and verification

- [WongBreakpointCells.lean](../real/WongBreakpointCells.lean): automatic cell geometry; all four selected endpoints passed the serialized check.
- [WongIntervalNormalization.lean](../real/WongIntervalNormalization.lean): generic finite interval representation and restriction/contraction closure; compiler exit code 0, with all six selected endpoints using only standard axioms.
- [WongSimplification.lean](../real/WongSimplification.lean): automatic composition, unique-parent preservation, sample-support condition, and breakpoint containment; all five selected endpoints passed, using only standard axioms. The checked draft hash was 46FA612EAFA5467D37017C28BD9E009FBD44A7EA3C84F14AC013D3041D0076E8; promotion changes only its introductory scratch-status comment.

The coordinator serializes all compiler activity. Independent mathematical and imported-interface review passed. The full 101-endpoint mathlib aggregate audit has passed for the promoted source. Hosted publication remains a commit-specific gate; these proofs do not establish correctness of external software or completion of the whole paper.



The current integrated source inventory is in [the core receipt](../verification/formal-audit.json) and [the mathlib receipt](../verification/real-audit.json). All selected endpoints use only the permitted standard axioms.
