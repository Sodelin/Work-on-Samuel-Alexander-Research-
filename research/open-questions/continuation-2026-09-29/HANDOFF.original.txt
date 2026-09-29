# Research handoff: checked universal-avoider and ordinal results

29 September 2026. This is a local handoff artifact, not authorization to publish.

Read [RESULTS.md](RESULTS.md) for the complete statements, proof explanations,
source attribution and limits. This task made no outbound submission or author
contact. Existing catalog entries and the other publication lane were left
unchanged.

## Prior public evidence

- Original source: Alexander, EJC 20(1) P31 (2013), Section 6, published page 12.
- Existing scoped answers are on unmerged draft
  [PR #6](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/pull/6).
- Inspected current head: `01db8c4cbb82000950ff7d3e7252b5438416c7c3`.
- Its nine earlier embedding/ordinal Lean source blobs are unchanged from the
  successful hosted proof checkpoint `8fd86430e78fed06fffe35df2fa85f28bdff48d9`.
- That earlier hosted run is historical evidence. No hosted run was returned
  for the current PR head itself. Selected prior modules were freshly compiled
  in this task with installed pinned dependencies.

## New local results

1. `TerminalCloneAvoiders.avoiding_no_countable_exact_parent_family_from_any_population`:
   every actual avoider yields an avoider with exactly one parent of each label,
   the same roots, and no injection into any specified countable population
   family at any finite global edge-stretch bound. Parent selection can shrink
   language; terminal cloning preserves the selected language exactly. Terminal
   vertices are permitted. A fixed child cap is not preserved.
2. `GenericPruning.start_core_iff_realizes_from` and
   `realizes_iff_surviving_start`: arbitrary vertex/label types, finite branching
   per label, exact actual path realization from a specified start iff the
   corresponding reachable state survives every finite pruning round. The core
   is a greatest fixed point. This concerns states, not an artificial-root tree.
3. `GenericMortalRank.height_attained_and_bounds`, `height_least`, and
   `survives_iff_le_height`: states outside that core have exact finite heights,
   without any global avoidance premise.
4. `BlowUpRankInvariance.avoider_has_exact_rank_transport`: the original complete
   finite-fibre enlargement preserves the exact least attained rank at every
   projected reachable state. This enlargement differs from terminal cloning.

There are 42 new audited endpoints in four files and 21 earlier endpoints
rechecked. Final printed proof dependencies are standard axioms only. See
the combined `verification-manifest.json` and the per-module receipts.

## Claim boundaries for review or later publication

- Credit standard well-founded ranks, finite branching and the classical
  locally finite graph diagonal method. Novelty of these methods is not claimed.
- The results answer precise standard-embedding and ordinal-membership
  interpretations of the two questions. They do not settle every possible
  meaning of Alexander's broad wording.
- Do not present the ordinary matching-history rank omega or Schmidt rank 1
  as a hierarchy separating avoiders. Both collapse in the source model.
- Do not describe the new generic state proof as a generic formalization of
  the distinct artificial-root history or Schmidt-rank calculations.
- The new source is local and has not been incorporated into the public branch.
- Separate AI audits and Lean verification are not independent human expert
  review or evidence of historical priority.

No decision has been made here about extending the program to a fixed child
cap, unbounded edge stretch, or a new biological observation model.
