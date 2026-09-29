# Current membership can hide the history needed for a split

**Verified:** `MergeHistoryProjection.lean`, Lean 4.33.1, eight audited endpoints, exit 0, no warnings/errors, and only standard Lean axioms. This is a structural operator model linked to a pinned implementation. It is not verification of the complete simulation or a solution of the source paper's broader open questions.

## The witness

There are four persistent sites, 0, 1, 2, 3. A current player is a binary tree recording the mergers that formed it. A forest is legal when each site occurs exactly once. The observation discards those trees and retains the **unordered set of unordered member sets**.

Two histories start from the same four separate players:

```text
left:   merge(0,1), then merge({0,1},2)
right:  merge(1,2), then merge(0,{1,2})
```

Site 3 remains a separate spectator. Both histories can be performed by merging adjacent roots in the ordered forest [0,1,2,3]. This formal adjacency is list adjacency; board geometry is covered only by the separate implementation test. Both finish with the identical observed partition:

```text
{{0,1,2}, {3}}
```

The explicit control is to split the designated composite into its **immediate predecessor trees**. In both witnesses, the first root has the same site support {0,1,2}; thus the control selects the same current group in both states. The differing result comes from its predecessor grouping with that target held fixed. The results are:

| History | Partition after the same split control |
|---|---|
| left | {{0,1}, {2}, {3}} |
| right | {{0}, {1,2}, {3}} |

The membership partition at present has forgotten which predecessor grouping formed the composite. That grouping is necessary for this restoration operation.

## What Lean proves

- Both two-step adjacent-merge histories compute to the stated forests.
- The initial, intermediate, and final forests are legal.
- Both designated composites admit the split and retain the spectator.
- Their current partitions are equal as `Finset (Finset (Fin 4))`, so the equality is independent of block and member ordering.
- Their restored partitions differ.
- The observation fails `ExactAbstraction.FibreCompatible` for the explicit split action. On the attainable observation type, the shared factorization theorem rules out an exact deterministic reduced update.
- More strongly, `no_partition_only_admissible_split` rules out a deterministic partition-only split even when correctness is required only on states where the designated split is admissible, and even when its output may be an arbitrary block family.

The executable split function is totalized by a no-op when the first root is not composite. The last theorem uses only admissible states, so the obstruction does not depend on that totalization choice.

## Implementation connection and evidence boundary

The independently reviewed source is [IPDm, commit eca9b122480b8c654081d6a844176417aefbbcae](https://github.com/lksshw/IPDm/tree/eca9b122480b8c654081d6a844176417aefbbcae). In [core/helperfunctions.py, merge lines 111–145 and split lines 153–174](https://github.com/lksshw/IPDm/blob/eca9b122480b8c654081d6a844176417aefbbcae/core/helperfunctions.py#L111), merging stores immediate predecessor IDs and splitting reactivates those predecessors. The relevant helperfunctions.py SHA-256 is `edaacacbb6f09810c0acd9fcbf7642610695501952b04eb59fb0d6a7a2e7a5a4`.

The independent operator test executes those original operators and structural helpers on an actual 2x2 eight-neighbour board, with explicitly mocked constructors and scalar NumPy helpers. It reports equal current partitions and active IDs {3,5}, with identical current tested metadata before splitting ID 5; the stored parent pairs are {2,4} versus {0,4}, producing the two partitions above. The fourth site supplies an opponent/spectator. That receipt is `independent-ipdm-operator-test.json`, separate from the Lean proof.

Equality of newly allocated active agent IDs and current controller metadata is established only by the separately scoped implementation test. The Lean trees retain persistent **leaf site IDs** and predecessor structure. They do not implement newly allocated agent IDs, policy, memory, score, source parent ordering, board geometry, or the stochastic mechanism that selects actions. Tree ordering is used to exhibit adjacent merges; the observation and output claims discard ordering. The source-level test and the Lean structural theorem therefore provide different kinds of evidence. Full stochastic policy reachability and complete program refinement remain unproved.

This target responds to the changing-player merge/split question discussed in section 6.4.3 of [Abramsky et al., DOI 10.1098/rsos.261059](https://doi.org/10.1098/rsos.261059). The published IPDm paper's full text was not part of the implementation review. The formal contract is a bounded interpretation sharpened from the source operator, with no novelty claim.

## Exact scope of the obstruction

The theorem rules out one deterministic update based only on the current partition that is exact for both admissible history states. It does not prove that the partition process is non-Markov under every distribution, nor does it exclude a stochastic mixture once a conditional distribution over hidden histories is fixed. No Lean entropy theorem is claimed.

## Receipts

- `merge-validation.txt`: final compiler and axiom output.
- `merge-verification.json`: private local provenance and artifact hashes.
- `PUBLIC-VERIFICATION.json`: portable combined receipt for both modules, with relative artifact names and 16 selected endpoints.
- `verification.json`: the generic module's separate eight-endpoint receipt.

Both final Lean source files use LF line endings. The generic proof source is frozen separately from this instance.
