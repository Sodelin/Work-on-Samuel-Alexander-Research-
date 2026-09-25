# Individual finite-edit additive constants: exact finite algorithm

## Result and verification status

The original all-edit-length refinement is solved: every fixed target that agrees with Thue–Morse from some index m onward has an exact, attained optimal integer additive constant, computable by a finite search with an explicit cutoff. This is stronger than the previously checked sharp allowance uniform over all edits and the separate exact height at each chosen start.

All five proof modules passed their individual Lean checks in the refinement staging area, including the complete global reduction and least-constant equivalence. Their twelve selected endpoints reported only permitted standard axioms, with no `sorryAx` or new axioms. They have been promoted to stable core module names; the refreshed 405-endpoint core aggregate check of the promoted imports has passed. The aggregate receipt, rather than the earlier published packet, determines the final integrated verification status.

The stable modules are [FiniteEditBranch](../lean/SamuelAlexanderResearch/FiniteEditBranch.lean), [FiniteEditGap](../lean/SamuelAlexanderResearch/FiniteEditGap.lean), [ThueMorseWindow](../lean/SamuelAlexanderResearch/ThueMorseWindow.lean), [FiniteEditAlgorithm](../lean/SamuelAlexanderResearch/FiniteEditAlgorithm.lean), and [FiniteEditOptimum](../lean/SamuelAlexanderResearch/FiniteEditOptimum.lean).

## Exact statement and executable procedure

Fix any m in the natural numbers, including zero, and any target s with s(k)=t(k) for every k at least m. No assumptions are imposed on the first m bits. Let L_s(v) be the actual attained maximum matching length from v in the existing BinaryAvoidance graph for s. The previously certified function `FiniteEditExact.height s m v` computes this length under the agreement hypothesis.

Define

```math
\delta_s(v)=3L_s(v)-8v,\qquad
N(m)=3\cdot 2^{m+3}+m,
```

and compute the integer

```math
B_s=\max_{1\le v\le N(m)}\delta_s(v).
```

Then:

1. Every positive start satisfies 3L_s(v) at most 8v+B_s.
2. A positive start no greater than N(m) attains equality.
3. For every integer B, the bound with B holds at all positive starts if and only if B_s is at most B.

Thus B_s is the exact smallest integer additive constant for this individual target. The procedure is: compute N(m), evaluate the certified height at each start from one through N(m), and take the maximum of the resulting integer residuals. In Lean, this is the executable expression

```lean
FiniteEditAlgorithm.best s m (FiniteEditAlgorithm.cutoff m - 1)
```

Here `best s m n` scans exactly the positive starts from one through n+1. The final equivalence quantifies over actual `IsMaximumPrefix` statements; it does not define the desired conclusion into a new height predicate.

The cutoff is deliberately generous and exponential in m. This result asserts termination and exactness, not a useful runtime bound or a minimal search cutoff. It also does not assert that every target attains the universal allowance 8m-1. Together with the previous uniform theorem, the new result gives the bounds -1 at most B_s at most 8m-1.

## Proof of the finite reduction

The proof combines actual matching paths, exact dyadic height bounds, and a finite-window identity. It does not infer a universal statement from numerical searches.

First, every sufficiently large dyadic extremal suffix admits an edited prefix. For q=2^n with q at least m+1, take the existing shifted matching suffix beginning at time m and vertex 3q+m-1. Its total extended length is 8q-3. The established backward-prefix construction supplies the first m edges with the edited target labels. Its start lies between 3q-m-1 and 3q-1, and is positive. The resulting residual is at least -1. Choosing n=m+2 gives a witness inside the finite search. Therefore its finite maximum is at least -1.

Second, the complete unedited height table gives a quantitative gap: every natural start a either equals 3 times a power of two minus one, or its unedited maximum is at most a+1. The even exceptional start a=2 belongs to the dyadic family and is retained explicitly.

Third, the new branch-separation theorem states:

> For q=2^n, if 2m is at most q, every original Thue–Morse matching path beginning at 3q-1 and lasting at least 4q has vertex 3q+m-1 at time m.

This applies to every such path, not merely an extremal witness selected by a construction. For q=2r, the proof examines the path at time r. Its minimum possible vertex is 7r-1. If it were at least 7r, the explicit competing boundary trajectory would put its vertex at time 8r at least 20r-1. The already checked dyadic upper boundary requires every reachable vertex at that time to be strictly below 20r-1. This contradiction forces the midpoint to be 7r-1, hence every preceding step to have length one. The smallest dyadic case is handled directly.

Fourth, the local Thue–Morse window around 3 times a power of two is determined by the parity of the exponent. The checked identities are

```math
t(3\cdot2^n+j)=t(j) \quad(0\le j<2^n),
```

and

```math
t(3\cdot2^n-r)=\bigl(1\mathbin{\mathrm{xor}}(n\bmod2)\bigr)
                    \mathbin{\mathrm{xor}}t(r-1)
\quad(1\le r\le2^n).
```

Consequently, if q=2^n and Q=2^M both exceed 2m+2 and the exponents have the same parity, the first m edges of a path ending at 3q+m-1 can be translated to edges ending at 3Q+m-1. All queried graph rows are beyond the edited region; the proof first applies the existing row-agreement theorem and then the window identities. The translated edges retain their actual edited target labels. Appending the established shifted extremal suffix gives an actual matching path of length 8Q-3. This is the checked `relocate_canonical_prefix` theorem.

To finish, suppose a start v greater than N(m) improved the finite maximum. Since that maximum is at least -1, the improving integer residual is nonnegative. Transport a longest edited path to an original Thue–Morse path of the same length. The transported start a lies within m of v, and the paths agree from time m onward.

If a is not dyadic extremal, the gap bounds its length by a+1. The original edited residual is then at most 3m+3-5v, contradicting its nonnegativity. Hence a=3q-1. The large-start inequalities imply q>2m+2 and length at least 4q. Branch separation forces the common time-m vertex to be 3q+m-1. The original sharp bound also limits the length to 8q-3.

Choose M to be one of m+2 and m+3, with the same parity as the original exponent. Both representative scales satisfy the needed window bounds. Translate the actual edited prefix to Q=2^M and append its sharp suffix. If v' is the new start, the proof obtains

```math
v'+3q=v+3Q,\qquad 1\le v'\le3Q-1\le N(m).
```

The new path's residual is at least the old path's residual, because its length is 8Q-3 while the old length is at most 8q-3. Its actual maximum length can only increase that residual. This contradicts improvement over the finite maximum and proves the global bound. Finite attainment then proves the exact least-constant equivalence.

## Checked endpoint map

| Module | Selected endpoints and role |
| --- | --- |
| `FiniteEditBranch` | `bad_boundary_join`, `branch_separation`: the competing trajectory and forced initial segment. |
| `FiniteEditGap` | `off_extremal_gap`: the height gap outside the dyadic extremal family. |
| `ThueMorseWindow` | `reflected_window`, `same_parity_left_window`, `same_right_window`: exact local-window identities. |
| `FiniteEditAlgorithm` | `best_attained`, `sharp_tail_witness`, `best_at_cutoff_ge_neg_one`: executable finite maximum, actual edited witnesses, and its lower bound. |
| `FiniteEditOptimum` | `residual_le_finite_best`, `individual_optimum_attained`, `individual_additive_constant_iff`: all-start reduction, global attainment, and the exact smallest integer constant. |

## Refinements and limits that remain distinct

The earlier proposed smaller search, combining starts through 7m+8 with two explicit backward traces, remains a potential optimization. The present checked algorithm does not need that stronger formula. Removing the finite exceptional-start search altogether is also not asserted. Earlier bounded experiments were used only to discover candidate lemmas; the Lean proofs above replace them as evidence for the all-m finite algorithm.

For m=1, the earlier checked universal theorem and equality witness already yield the mathematical subcase B_s=-1 when s(0) is false and B_s=7 when s(0) is true. The all-m theorem now covers both cases as part of the full result; no separate one-bit theorem substitutes for it.

The other original refinements remain visible and separate:

| Original refinement | Current completed result | Exact remaining target |
| --- | --- | --- |
| Joint phase/index digit description | Exact maxima are computable for every phase and start; phase zero has a certified finite digit recurrence. | A finite digit recurrence or closed form treating phase and starting index jointly, with its exact domain and any claimed complexity bound. |
| Optimal fixed-gender root count | The directed-line construction attains the optimal child cap two and has exactly three roots. | Whether three roots are necessary under the same avoidance and population requirements, or whether two roots can attain those requirements. The exact child-cap threshold does not settle this. |
| Crossing widths above the minimum | The minimal-width tail is exactly the kth power of a ray; finite-port encoding is available. | Structural classification at larger widths, including the binary width-four regime and its label-language behavior. The encoding alone is not a classification. |
| Natural or published cellular automata | The crafted three-state rule has a strict comparison between the specified static and stateful certificate classes. | A verified improvement for a natural binary or published rule, with its actual transition rule, evolution, certificate classes, and comparison against existing bounds. The synthetic example does not answer that target. |

This result concerns the established symbolic matching graph. It makes no biological inference about the Wong model and no literature-priority claim.

The current integrated source inventory is in [the core receipt](../verification/formal-audit.json) and [the mathlib receipt](../verification/real-audit.json). All selected endpoints use only the permitted standard axioms.
