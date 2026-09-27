# Predictive-memory continuation checkpoint

Date: 27 September 2026. Branch: `codex/royal-society-memory-2026-09-27`.
Base: `01db8c4cbb82000950ff7d3e7252b5438416c7c3` on the existing research draft
branch `codex/research-followup-2026-09-25`. Work was performed in a separate
checkout. The Wong continuation owns its new recorder/process files; none
are edited or imported here. Compiler use was serialized with the coordinated
OS lock. The primary source and all original proof files remain preserved.

## Exact artifacts

Proof-source commit: `6f4745a451ee3f47b79b76395ca5ef3ef6b60529` (five Lean modules
and replay tools; the preceding `55b6471` introduced the Lean statements).
The [proof receipt](verification/PROOF-RECEIPT.json) records the full commit
identifier, compiler, pinned Mathlib revision, and exact per-source and
per-log SHA256 values. `check_packet.py` compares every compiled source with
both the working file and its Git blob; the receipt remains authoritative
if this prose is read from a later documentation commit.

| File | Responsibility |
|---|---|
| `PredictiveState.lean` | Behavioral quotient, universal factorization, distinguishability, intervention restriction, depth certificate and conditional feedback preservation. |
| `ControlledMemory.lean` | Arbitrary-history parity bridge, lower bound, reachability, suffix-memory limitation and changed-probe witness. |
| `HistoryObservation.lean` | Stable-type/clock null, selection identities and arbitrarily delayed distinctions. |
| `AncestryObservation.lean` | Controlled destructive-restriction map and enlarged-sample counterexample. |
| `WongPredictiveBridge.lean` | Actual finite-gARG instantiation and completion-specific no-IAP-decoder consequence. |
| `verify.py` | Fresh private build of the project import closure and explicit axiom audit. |
| `check_examples.py` | Exact finite refinement and invented rational type/selection examples. |
| `check_packet.py` | Receipt/source/log hashes, exact Git inputs, local reading links and source-question status boundaries. |
| `.github/workflows/predictive-memory.yml` | Independent hosted replay of this packet. |

## Validation and integration

Final fresh replay: all **35 project modules** compiled; **56 new top-level
theorems and 16 historical selected endpoints** passed the transitive axiom
audit. Allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`.
These are declaration counts, including supporting lemmas, not discoveries
or solved author questions. The fresh committed-source replay passed with
`fresh_project_rebuild: true`; all compiled source bytes agree with their Git
objects. Hosted CI has its own run status and receipt, separate from this
local evidence.

The finite checker passed the complete eight-state comparison and the two
exact rational counterexamples. The previous bridge checker reproduced every
non-timestamp field in its frozen receipt; its new timestamp/output is kept
separately in [CONTROLLED-REPLAY.json](verification/CONTROLLED-REPLAY.json).
The [old rare-event replay](verification/CALIBRATION-REPLAY.json) again passed
15 cases and 834 deterministic rules; its arbitrary-size probability proof
remains written, not Lean checked.

The [independent scope review](INDEPENDENT-SCOPE-REVIEW.md) is a statement and
source review, not a separate compiler run. The public reading page is
[TIME-AND-MEMORY.md](../../../../TIME-AND-MEMORY.md). The canonical
[ledger](../problem-ledger.json) still marks every full author question open.
Integration is a separate draft PR against the existing research branch;
neither that parent draft nor this continuation is assumed merged.

## Remaining gates

The ordered continuation contracts are in [AUDIT.md](AUDIT.md), with the
stochastic pushforward contract and biological discrimination criteria in
[BIOLOGY.md](BIOLOGY.md). The leading mathematical gap is stochastic
intervention-law preservation; the leading evidence gap is a justified
biological observation/intervention model. The rare-event theorem needs its
finite probability proof, and the changing-agent source problem still needs
controller/payoff/legality semantics. The fixed-locus ancestry result does not
provide the separate marked-generator map.

No task was archived. Completing this proof packet does not complete the
paper's broader agenda or trigger chat archival.
