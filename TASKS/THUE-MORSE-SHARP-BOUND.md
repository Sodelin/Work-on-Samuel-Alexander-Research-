# Research challenge: sharp Thue–Morse path length

**Status:** Both targets below and the exact equality set are proved and Lean checked. The independently reviewed [constructive proof](../research/thue-morse/NEXT-INVARIANT.md) is implemented in [SharpThueMorse](../lean/SamuelAlexanderResearch/SharpThueMorse.lean), using the actual bit sequence, all dyadic runs, the [interval theorem](../lean/SamuelAlexanderResearch/ThueMorseBound.lean), and a checked bridge to the original edge-labelled graph. The expanded [current audit](../verification/formal-audit.json) includes these endpoints. Exact first-hit and real-coefficient corollaries now have separate Lean theorems. External mathematical and prior-work review remain open. The original questions are retained for comparison with the completed proof.

Let `t(n)` be the parity of the binary digit sum of `n`. The vertices are the nonnegative integers. For each `w >= 2`, there are edges `(w-1) -> w` labelled `t(w)` and `(w-2) -> w` labelled `1-t(w)`; there is no edge `0 -> 1`. For a start vertex `v`, a path of length `ell` matches when its edge at index `k` is labelled `t(k)` for every `0 <= k < ell`. Let `L(v)` be the maximum matching length.

## Original questions, now resolved

1. Is `3*L(v) <= 8*v-1` for every integer `v >= 1`?
2. Is `L(3*2^n-1) = 8*2^n-3` for every integer `n >= 0`?

The [earlier note](../notes/THUE-MORSE-PATHS.md) proves the weaker quadratic bound using overlap-freeness and records two finite scans. The sharper proof instead follows exact boundary trajectories at arbitrary dyadic scale; it does not require overlap-freeness or infer a universal theorem from a finite scan.

The reproducible command `python research/thue-morse/sharp_check.py` passes 18 complete trajectory replays, 8,140 advance comparisons, and 256 bounded first-hit checks, and compares the inequality and exact equality set with the existing scan. These finite diagnostics corroborate indexing; the universal claims have separate Lean proofs.

## Original deliverable and acceptance checks

- State the exact theorem or counterexample, including all quantifiers, the missing `0 -> 1` edge, and the target starting at `t(0)`.
- Give a complete argument that an independent mathematician can check. If the result is false, provide a finite path or recurrence witness showing the first failure and replay it with a separate checker.
- Audit the claim against the known quadratic proof and at least one primary source on Thue–Morse word structure. Distinguish an original argument from a known theorem used as a lemma.
- If formalizing in Lean, use a pinned toolchain and record the exact formal statement, assumptions, `#print axioms` output, and successful build. No `sorry`, opaque extra axiom, or finite computation substituted for an infinite claim. A correct prose proof without Lean is valuable but must be labelled as such.
- Return a small repository patch or PR, a one-paragraph explanation of what changed, exact verification commands, and any remaining gap. Do not relabel the finite scan as proof.

The original suggested attack was to derive recurrences for reachable frontiers under `t(2n)=t(n)` and `t(2n+1)=1-t(n)`, then control how the offset blocks interact. The completed proof uses the exact interval reduction and explicit dyadic boundary trajectories.
