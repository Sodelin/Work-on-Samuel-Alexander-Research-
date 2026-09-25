# An actual finite gARG reconstruction boundary

**Status:** Lean 4.33.1 compilation passed with exit code 0. All five printed endpoints passed the standard-axiom audit.

`real/WongExamples.lean` places the sample-reconstruction counterexample inside the finite interval-annotated gARG structure. Both examples have the same genome type `Fin 3`, so their node catalogs are exactly `{0,1,2}`. Their sample sets are both `{2}`. There is no hidden loss of node identifiers, unary-node suppression, empty annotation, or duplicate-record encoding.

| Graph | Stored parent-to-child edges |
| --- | --- |
| `splitGARG` | `0 → 1` on `[0,1)`; `1 → 2` on `[1,2)` |
| `tailGARG` | `1 → 2` on `[1,2)` |

Every record has one proper half-open interval. Both graph structures carry proofs of acyclicity. Additional theorems prove nonempty annotations, canonical records, and a unique local parent for every child at every natural-number coordinate.

When ancestry is extracted by tracing from sample 2 at a single coordinate, both examples yield exactly the same relation:

| Coordinate | Extracted edges, in both examples |
| --- | --- |
| `0` | None |
| `1` | `1 → 2` |
| `x ≥ 2` | None |

The equality theorem quantifies over **all** natural-number coordinates and **all** nodes, rather than checking the table by bounded testing. At coordinate 0 the sample has no recorded parent; the extra edge `0 → 1` concerns ancestry of a different genome at that coordinate and is not visited. At coordinate 1 the edge `1 → 2` is retained. Thus the raw graphs differ despite identical sample-extracted local edge relations and the same node catalog.

`finite_garg_sample_reconstruction_boundary` bundles this full statement. `raw_locus_relations_differ` additionally witnesses that the lost information is an actual interval-supported edge, not merely a topological edge with empty annotation. `split_not_sampleSupported` and `tail_sampleSupported` identify precisely which hypothesis distinguishes the examples.

This concerns the scope of the reconstruction discussion in [Wong et al. (2024), Appendix E, journal pages 14–15](https://doi.org/10.1093/genetics/iyae100). It shows why reconstruction from sample-extracted relations must retain a sample-support qualification for unrestricted input graphs. It does not contradict recovery from complete local edge relations, or recovery of graphs already satisfying the support condition. The general exact criterion is proved as `WongGARG.GARG.extracted_eq_local_iff_sampleSupported`.

The counterexample is a mathematical witness. It does not supply a biological owner map, infer a real organism pedigree, demonstrate an empirical dataset error, or establish that the authors intended the unrestricted reading. No scientific novelty or comprehensive refutation of the paper is claimed.

## Verification receipt

The root agent ran the serialized Lean compiler against source SHA-256 `C0BA71964C11125AECC5E8425D2C1188A6D09086AFD1E941C07A538FD78B7D59` and reported exit code 0. All five printed endpoints use only permitted standard axioms (`propext`, `Classical.choice`, `Quot.sound`); the two concrete graph-definition audits include their acyclicity proofs. No dependency download or parallel build was launched by this lane. This per-module result remains distinct from hosted release CI or independent human review.


The compiler lane subsequently normalized line endings to LF without changing proof content. Current source SHA-256 after normalization: C0BA71964C11125AECC5E8425D2C1188A6D09086AFD1E941C07A538FD78B7D59. The fresh aggregate receipt will bind these normalized bytes.

