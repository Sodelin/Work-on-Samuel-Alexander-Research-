# Port dynamics: checked decoder and periodic universality

**Status: September 25, 2026.** Proposal 3 now has a compiled Lean proof that a complete eventually periodic slot schedule with actual incoming-label coverage realizes every infinite word. The path is strictly increasing and starts in a fixed finite block of births. The module also certifies the decoder's exact lifecycle and the degree and crossing-edge guarantees for legal fair schedules. The canonical graph-to-schedule construction and the converse from periodic graph adjacency remain separate formalization tasks.

This document describes the scope of [PortDynamics.lean](../lean/SamuelAlexanderResearch/PortDynamics.lean), which imports [FinitePhasePaths.lean](../lean/SamuelAlexanderResearch/FinitePhasePaths.lean). These results do not establish literature priority.

## 1. What the schedule records

There are $`C`$ fixed slots. Before each birth a slot stores an existing source index and a label. The schedule specifies which slots are consumed and what labels their replacements receive. Consumption emits an edge from the stored source to the current birth. Each replacement receives the current birth's index as its source; unselected slots retain their tokens.

`PeriodicAfter S M p` means that after schedule time $`M`$ the selected slots repeat after $`p`$ steps and replacement labels repeat on selected slots. Values of the replacement-label function on unselected slots have no effect and need not repeat. This is periodicity of the complete meaningful action, not merely of the slot count or unlabelled topology.

`IncomingCoverage S base initial` means that at every birth, every alphabet label occurs on some token actually consumed at that birth. It concerns the old token's label; an arbitrary assignment to replacement tokens is insufficient.

The decoder retains absolute source identities. A separate finite description can replace those identities by their equality partition and regenerate the identities during decoding. The finite quotient used by the proved language theorem is derived directly from the complete action schedule.

## 2. Main proved theorem

`PortDynamics.periodic_schedule_realizes_strict` assumes:

- an explicit schedule `S`, initial tokens, and initial birth index `base`;
- $`p>0`$ and `PeriodicAfter S M p`;
- `IncomingCoverage S base initial`.

For every label word $`s:\mathbb N\to A`$, it proves a path with

```math
\mathrm{base}+M\le v_0<\mathrm{base}+M+p,
\qquad
v_n<v_{n+1},
\qquad
\operatorname{DecodedEdge}(v_n,v_{n+1},s_n).
```

The quantified alphabet `A : Type` need not be explicitly finite. Incoming coverage using finitely many slots already restricts which alphabets can satisfy the hypotheses. The population-specific wrapper `Legal.periodic_realizes` uses `Fin k`.

The proof establishes the finite phase graph's incoming-label property in `phase_incoming`. Every quotient edge retains a positive displacement, and `lift_phase_path` proves that quotient paths lift to actual decoded edges. The quotient property and lifting property are conclusions of the implementation, not extra assumptions. The compactness step is `FinitePhasePaths.realizes_all`, proved for a finite phase graph with incoming edges of each label.

**Fairness is unnecessary for this language theorem.** Every sufficiently late consumed slot in a periodic schedule has a previous consumption within one period. Those active slots suffice for the proof. Permanently inactive slots contribute nothing to the path language. Fairness is required for the separate statement that *every* current slot represents an actual crossing edge and that each birth has the claimed full outgoing degree.

## 3. Checked decoder guarantees

| Endpoint | Hypotheses and exact guarantee |
| --- | --- |
| `decoded_birth_order` | If initial token owners precede `base`, every decoded edge points forward. |
| `token_origin`, `decoded_born_iff` | A decoded edge between tail births is exactly a token inserted at the source and consumed at its next use. |
| `decoded_label_unique` | Simple consumption ensures a single label per source-child pair. |
| `Legal.exact_incoming_parent` | One parent of each `Fin k` label, with an exact characterization of that parent. |
| `Legal.incoming_parents_injective` | The parents for different incoming labels are distinct. |
| `Legal.exact_outgoing_children` | Under fairness, each tail birth's children are exactly those indexed by its selected input slots. |
| `Legal.outgoing_children_injective` | The resulting indexing by `Fin k` is injective, giving exactly $`k`$ children. |
| `pending_crosses` | Under fairness and old initial owners, every current slot becomes a real crossing edge. |
| `crossing_from_slot` | Every decoded edge crossing the cut arises from a current slot. |
| `crossing_slots_injective` | Under simple consumption, different slots represent different source-child pairs. Together the preceding three endpoints give exactly $`C`$ crossing edges. |
| `bornEdge_shift_iff` | Tail-born edges and labels translate by the full action period. |
| `next_span_bound` | A tail token's next consumption, when it exists, lies within one period. |
| `fair_period_flush` | Every token present at a periodic cut is replaced within one period. |

The exact-degree and exact-width claims are represented by explicit injective and surjective indexing theorems, rather than by a new cardinality library or an assumed numerical count.

`Legal` records old initial sources, simple consumption, and an input map whose image is exactly the selected slots and whose consumed labels are exactly `Fin k`. Injectivity of the input map is proved from the distinct labels. Fairness is a separate property: every slot is selected at some time at or after every cut.

## 4. Remaining population construction

The existing `InfiniteConservation.eventual_structure` already supplies a constant-width tail with exact indegree and outdegree $`k`$. To complete the formal representation theorem, a further module must construct the canonical schedule from that population, not assume that the population admits such a schedule.

The intended output is a tail index `base`, width `C`, schedule `S : Schedule C (Fin k)`, and initial tokens satisfying:

1. `Legal S base initial` and `Fair S`.
2. For each child `v ≥ base`, original adjacency with label `a.val` is equivalent to `DecodedEdge S base initial u v a`.
3. `C` equals the actual conserved crossing count.
4. The encoding uses the specified canonical rule: initial crossing edges sorted by source then target; outgoing edges sorted by target and assigned to sorted freed slots.

The existing population stores labels as `Option Nat`. Exact tail indegree plus coverage of the first $`k`$ labels must therefore first exclude extra labels on edges targeting the tail. The adapter must also derive a finite enumeration of all crossing edges from their actual finite supports and count. Neither obligation is assumed or disguised as a conclusion in `PortDynamics`.

The reverse implication, from eventually translation-periodic labelled graph adjacency to an eventually periodic canonical schedule, still requires a finite deterministic-state proof. Sorted refilling may forget which consumed token occupied which freed slot, so the state evolution need not be invertible and may have a transient. The written proof uses bounded source ages, residual target distances, labels, and graph phase; it permits both a transient and a schedule period larger than the graph period.

## 5. Verification receipt and attribution boundary

The frozen module compiled with exit code zero and no warnings using the existing project toolchain:

```powershell
$env:ELAN_HOME='C:/Users/Owner/.elan'
lake env lean -o .lake/build/lib/lean/SamuelAlexanderResearch/PortDynamics.olean lean/SamuelAlexanderResearch/PortDynamics.lean
```

SHA-256: `445C6AC224B99C66199A157B8895161892954D1584053D2D3440B6F7E4FECD7D`.

Ten central `#print axioms` reports contain exactly `propext`, `Classical.choice`, and `Quot.sound`. There are no `sorry` terms or declared axioms. This receipt covers the local module compilation; the integration task owns the repository-wide build and publication.

Finite-state graph encodings and finite-graph compactness have established predecessors. These modules certify the stated definitions and deductions; they do not establish that the encoding or periodic-universality result is new to the literature. Prior-art comparison, including slice encodings and omega-regular language results, remains a separate source-audit obligation.
