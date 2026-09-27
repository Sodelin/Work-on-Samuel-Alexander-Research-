# Measurable validity and intrinsic-law support

Sources: `real/WongMarkedSupport.lean` and `real/WongDatedSupport.lean`.
Status: **PASS**. `WongMarkedSupport` compiled on its first run in 27.153 seconds (18-project-module closure). `WongDatedSupport` compiled on its first run in 27.719 seconds (20-project-module closure). The five selected axiom checks use only `propext`, `Classical.choice`, and `Quot.sound`. Source-hashed receipts, compiler logs, and `SUPPORT-VERIFICATION.json` are preserved here. The parent lane owns the combined exact-commit replay.

The raw validity predicate includes exact coverage at **all real genome coordinates**. A finite family of half-open intervals has a common right neighborhood of any x<L on which its entire slot-membership pattern is unchanged. A rational coordinate in that neighborhood detects exactly the same IDs. The checked `coverage_iff_rational` therefore reduces real-locus exact coverage to a countable family of rational-coordinate tests. Each test preserves lineage identity even when intervals or endpoint vertices coincide. Together with the other discrete and real-coordinate comparisons, this gives a Borel predicate in the already fixed natural raw-state sigma algebra.

This is an infinite countable mathematical test set. It does not claim that finitely observed genomic loci identify the graph, a pedigree, or a species-like cluster.

The user supplied an independent supporting argument through the side chat: **Side proof handoff: measurability of valid marked histories**, at `C:/Users/Owner/Documents/Codex/2026-09-27/wong-side-validity-01a0e0ef/PROOF-HANDOFF.md`. That argument tests the finite set of all recorded interval endpoints plus the genome's lower endpoint, choosing the greatest endpoint at or below each query coordinate. Its proof handles shared endpoints and distinguishes slot IDs. It is a complete written mathematical argument with finite sanity checks, explicitly **not Lean checked**. We read it before completing integration and retained the already drafted rational-witness proof instead of duplicating the finite-endpoint implementation.

The two routes establish the same measurability conclusion but have different test sets: the side argument uses finitely many data-dependent endpoint coordinates, while the Lean proof uses all rational coordinates in the genome. Neither is a theorem that an arbitrary fixed finite set of biological observations suffices.

The side handoff also independently describes the subsequent route used in the dated-support proof: derive measurable equality from the injective full-field encodings; eliminate the uncountable existential state witness using the optional result's decoded value and presence flag; prove the remaining natural-index and chronological comparisons measurable; then apply `ae_map_iff` to the already established input-space validity theorem. This proves a validity statement under the actual output history law without changing its sigma algebra or model.

Independent handoff SHA256: 2ae6ffcb2ca8d8e8c99cd8b231ae31fb3c10faeeb5df514da6816489713fb081.


## Checked theorem inventory

| Theorem | Exact role |
| --- | --- |
| `WongMarkedSupport.rational_slot_pattern` | For every raw state and real x<L, some rational q strictly between x and L has exactly the same membership in every allocated interval, preserving lineage ID. |
| `WongMarkedSupport.coverage_iff_rational` | Exact unique-slot coverage at every real coordinate in [0,L) is equivalent to its rational-coordinate tests. |
| `WongMarkedSupport.measurable_valid` / `measurableSet_valid` | All raw validity fields, including real-locus coverage, define a Borel set under the existing full natural encoding. |
| `WongDatedSupport.validDated_iff_decoded` | The optional final record and its presence flag eliminate the apparent uncountable existential over raw states without weakening the predicate. |
| `WongDatedSupport.measurable_validDated` | The intrinsic dated-history validity predicate, including final state, stopping plateau, and strict chronological order of every completed edge, is Borel. |
| `WongDatedSupport.historyLaw_ae_validDated` | For L>0, n>0, a>0 and b>=0, the actual output `historyLaw` at the normalized parameter assigns probability one to `ValidDated L n`. |

The dated module derives measurable equality from each injective full-field numerical code, including the entire countable slot and parent functions and event record list. No top sigma algebra on real cuts or measure-dependent output sigma algebra is introduced.

No proof obligations remain in these two modules. Two linter suggestions remain on the reusable `measurableEq_of_injective_code` class-valued definition (reducibility annotation and using `theorem` for a proposition); compilation and all selected axiom checks passed. This support result describes the marked Big-ARG realization already built in the parent modules. It does not add an organism pedigree, finite-observation identifiability, a biological species classification, or source claims beyond that realization.

Reproduce from the isolated checkout with `python -X utf8 research/wong/continuation-2026-09-27/check.py WongDatedSupport`. The wrapper acquires the shared compiler lock and rebuilds stale import objects before checking the module.
