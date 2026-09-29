# Controlled abstraction bridge

General connections cycle 1, 25 September 2026. This packet presents a written bridge connecting a finite cell-state model and a history-sensitive decision model through exact prediction-preserving abstraction. A finite cell-state toy discards a nuisance bit; a history-sensitive decision device discards its full record while retaining parity. The retained two-bit description is coarsest for the stated actions and observation target; adding a probe makes a visible-state-only description fail.

## Evidence and limits

The prior Q04 and Q09 results remain the already-checked programme evidence at commit `138dd529643ae5706a9df6a750bd6344ab967a8a`: 16 selected Lean endpoints in total, 8 in `ExactAbstraction` and 8 in `MergeHistoryProjection`. The two original Lean modules and their public verification receipt are included as byte-identical copies at their canonical repository paths, with hashes recorded in this packet's source/publication manifests. Byte-identical copies are also included in this packet's `source-snapshots/` directory because the unchanged Python checker reads them there. They are reused results; this cycle ran no Lean checks.

The cell and decision examples, their exact maps, and the H refinement argument are written derivations. The included Python script performs bounded finite checks only. It does not prove the arbitrary-record or all-horizons statements, and no new Lean proof, empirical validation, novelty result, or biological claim is made. An existing broader synthesis is mentioned in BRIDGE.md as an internal-intake reference; it is not included here and this packet makes no public reproduction claim for it.

## Files in this packet

- [Bridge and worked examples](BRIDGE.md)
- [Sources and evidence limits](SOURCES.md)
- [Public-safe source manifest](SOURCE-MANIFEST.json)
- [Bounded Python checker](check_models.py)
- [Frozen finite-check results](FINITE-CHECKS.json)
- [Scoped independent review](SOL2-REVIEW.md)
- [Publication allowlist and hashes](PUBLICATION-MANIFEST.json)
- [Replayed finite-check receipt](REPLAY-RECEIPT.json)
- [Prior ExactAbstraction module](../exact-abstraction/ExactAbstraction.lean)
- [Prior MergeHistoryProjection module](../exact-abstraction/MergeHistoryProjection.lean)
- [Prior public verification receipt](../exact-abstraction/PUBLIC-VERIFICATION.json)

To rerun the Python checks, use a disposable copy of this packet and run `python check_models.py` from its root. The unchanged checker reads `ExactAbstraction.lean`, `MergeHistoryProjection.lean`, and `PUBLIC-VERIFICATION.json` from the included `source-snapshots/` directory. Their canonical sibling copies remain available at `../exact-abstraction/`; all six source files are byte-identical. The checker rewrites `FINITE-CHECKS.json` with a fresh timestamp, so keep the frozen file and run only in the disposable copy. The separate replay receipt compares all other result fields.

