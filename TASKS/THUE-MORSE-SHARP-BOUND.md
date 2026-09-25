# Research challenge: sharp Thue–Morse path length

**Goal:** Prove or refute the two conjectures below for the exact population and indexing specified here. A finite search, however large, is evidence and does not finish this task.

Let `t(n)` be the parity of the binary digit sum of `n`. The vertices are the nonnegative integers. For each `w >= 2`, there are edges `(w-1) -> w` labelled `t(w)` and `(w-2) -> w` labelled `1-t(w)`; there is no edge `0 -> 1`. For a start vertex `v`, a path of length `ell` matches when its edge at index `k` is labelled `t(k)` for every `0 <= k < ell`. Let `L(v)` be the maximum matching length.

## Questions

1. Is `3*L(v) <= 8*v-1` for every integer `v >= 1`?
2. Is `L(3*2^n-1) = 8*2^n-3` for every integer `n >= 0`?

The [current note](../notes/THUE-MORSE-PATHS.md) proves the weaker bound `L(v) <= (v+1)(v+6)/2`, using the classical overlap-free property of Thue–Morse. Two distinct frontier engines found no counterexample to Question 1 for `1 <= v < 131072`, and equality appeared precisely at the proposed family points with `n <= 15` in that range. Their code and finite outputs are in [`checks/`](../checks/). Neither conjecture has been proved here.

## Deliverable and acceptance checks

- State the exact theorem or counterexample, including all quantifiers, the missing `0 -> 1` edge, and the target starting at `t(0)`.
- Give a complete argument that an independent mathematician can check. If the result is false, provide a finite path or recurrence witness showing the first failure and replay it with a separate checker.
- Audit the claim against the known quadratic proof and at least one primary source on Thue–Morse word structure. Distinguish an original argument from a known theorem used as a lemma.
- If formalizing in Lean, use a pinned toolchain and record the exact formal statement, assumptions, `#print axioms` output, and successful build. No `sorry`, opaque extra axiom, or finite computation substituted for an infinite claim. A correct prose proof without Lean is valuable but must be labelled as such.
- Return a small repository patch or PR, a one-paragraph explanation of what changed, exact verification commands, and any remaining gap. Do not relabel the finite scan as proof.

Suggested first attack: derive recurrences for reachable frontiers under `t(2n)=t(n)` and `t(2n+1)=1-t(n)`, then try to control how the offset blocks interact. This is a suggestion, not an assumption that the conjecture is true.
