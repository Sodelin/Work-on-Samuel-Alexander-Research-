# Finite interval re-encoding after ancestry transformations

**Integrated aggregate check passed: 405 core endpoints and 101 mathlib endpoints.** The coordinator reports successful compilation with all six selected endpoints restricted to standard axioms. The accepted source is [WongIntervalNormalization.lean](../real/WongIntervalNormalization.lean).

The new theorem constructs an actual finite interval-annotated gARG from a relation specified on a supplied finite family of proper, pairwise-disjoint half-open cells. Within each cell, the indexed relation must equal its value at the lower endpoint. Every coordinate supporting an edge must lie in one of the cells. The family may have unused gaps and does not need a list-storage order.

One record is constructed for each ordered parent–child pair with at least one active cell. Its regions are exactly the cells where that pair's relation holds. This directly proves nonempty annotations and canonical records: there is one record per active endpoint pair, even when the relation occupies several separated cells. It does not merge adjacent active cells or minimize the number of interval fragments.

`CellPresentation.finite_cell_representation` returns a gARG with the requested sample set, exact inheritance at every coordinate, and topology exactly equal to the union of the indexed relation. It requires **acyclicity of that union**. Merely knowing that every individual local graph is acyclic would be insufficient: one coordinate may have `a → b` while another has `b → a`. In applications to an existing gARG, the common original DAG supplies the stronger condition.

The module then proves that sample-ancestry restriction and contraction with a fixed retention predicate preserve the supplied cell decomposition. Restriction only removes edges. Each contracted edge represents a nonempty original path at the same coordinate, so it cannot create support outside the original cells. Constancy transports through ancestry reachability and hidden-path contraction. Global union acyclicity also survives: a contracted edge maps to an original topology path, and cycles would map to cycles.

Three application endpoints return finite interval output for actual input gARGs:

- `sample_restriction_representable`: exact sample-extracted local relations, with the same sample catalog and canonical nonempty records.
- `extracted_contraction_representable`: exact sample-extracted then contracted local relations, again represented by actual gARG records.
- `reencoded_contraction_sample_paths`: the output preserves exactly original fixed-coordinate ancestry from retained starting nodes to retained sample nodes.

These applications retain the original finite node type. Unretained nodes become isolated; the theorem does not physically remove them from the catalog. The retention predicate is fixed across coordinates. A coordinate-dependent retention rule would need its own finite-cell constancy hypotheses. The companion [automatic simplification theorem](WONG-SIMPLIFICATION.md) now discharges support coverage, pairwise disjointness, and constancy using cells derived from the actual input breakpoints. The generic theorem here keeps those hypotheses explicit so it also applies to other finite cell presentations.

The construction is mathematical and uses classical decidability. It is not an executable interval compiler, a tskit implementation, a record-format roundtrip, or a complexity/optimality result. Its topology describes the union of active genomic relations; empty-annotation ghost edges in a permissive input representation are not preserved by that union.

## Verification

Root-serialized Lean check: exit code 0 for source SHA-256 2A1E4990EE21DF0FE2A117E877CFB5E93BD0FADD84C98969A2F382CB83F5D8BA; all six selected endpoints passed the permitted-standard-axiom check. Independent mathematical and imported-interface review also passed. The accepted module imports `WongAlexander` and `Mathlib.Data.Fintype.Prod`. Promotion changes only the introductory scratch-status comment. The promoted source also passed the complete 101-endpoint mathlib aggregate audit; its exact source hash is recorded in verification/real-audit.json. Hosted publication is a separate commit-specific gate, and no complete formalization of the paper is claimed.


The current integrated source inventory is in [the core receipt](../verification/formal-audit.json) and [the mathlib receipt](../verification/real-audit.json). All selected endpoints use only the permitted standard axioms.
