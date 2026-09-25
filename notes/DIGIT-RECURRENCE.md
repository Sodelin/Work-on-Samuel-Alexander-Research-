# Certified integer digit recurrence for actual Thue–Morse heights

`DigitRecurrence.evaluate_isMaximum n` proves that the executable digit
algorithm computes an attained maximum of actual matching paths in `P_t`,
for every natural start `n`, including zero. Its hypotheses do not include
a candidate formula or a supplied graph-height sequence.

The proof has two independently established parts. `FullHeight.height_formula`
proves the closed form for actual graph maxima. This module derives every
integer digit transition universally from that formula, then composes the
two results. It does not use the old sampled transition data as a premise.

## Coordinates and complete table

At index `n`, let `H` denote the actual maximum matching length. The ten
integer coordinates are

```math
(1,T,U,V,L,E,O,X,F,C),
```

where

```math
\begin{gathered}
T=t(n),\quad U=t(n+1),\quad V=TU,\quad L=H(n),\\
E=H(2n),\quad O=H(2n+1),\quad
X=\frac{H(4n+1)-t(n)}2,\\
F=H(4n+2),\quad C=H(4n+3).
\end{gathered}
```

Boolean bits are represented by the integers zero and one. The initial
vector is `(1,0,1,0,1,1,0,0,5,0)`. The checked transformations are:

| Coordinate | At `2n` | At `2n+1` |
|---|---|---|
| `1` | `1` | `1` |
| `T` | `T` | `1-T` |
| `U` | `1-T` | `U` |
| `V` | `0` | `U-V` |
| `L` | `E` | `O` |
| `E` | `3-2T-2U+2V` | `F` |
| `O` | `2X+T` | `C` |
| `X` | `T` | `3U-12V-2E+2X+F` |
| `F` | `7-7T-2U+2V` | `T+3U+15V+4E-4X` |
| `C` | `5X+2T-3V` | `3C-2O` |

`X_integral` proves the exact identity `H(4n+1)=2X+t(n)` before division
is interpreted as an integral coordinate. `coordinate_X` and `X_values`
prove that `X` is always one of 0, 1, 4, or 6. The use of integer division in
the executable coordinate definition therefore loses no information.

## Universal derivation

`odd_times_power` proves that every positive integer can be written as
`(2h+1)*2^r`. Applied to `n+1`, this gives an exhaustive decomposition, rather
than a tested range of indices. The actual Thue–Morse recurrences give

```math
t(n+1)=1-t(h),\qquad t(n)=t(h)\mathbin{\mathrm{xor}}(r\bmod2).
```

The even-digit rows follow directly from the closed-form rows at scales one
and two. The only substantial odd-digit rows, for `X` and `F`, are split into
`r=0`, `r=1`, and `r>=2` in `odd_auxiliary`. The exceptional even-height row
at scale two is retained. For `r>=2`, `n` is congruent to 3 modulo 4, so its
special-case bit vanishes; for `r=1`, that bit is exactly
`!t(h) && t(h+1)`. Each remaining Boolean case is proved by integer arithmetic.

The last odd-digit row follows because every branch of `oddValue h r` is
affine in `2^r`, with its correct branch-dependent intercept, including the
special intercept `-3`. `oddValue_scale` proves the required identity at
three successive scales without discarding natural-subtraction boundaries.

The main intermediate results are `even_transition`, `odd_transition`, and
`digit_recurrence_of_formula`. Their explicit `FormulaSpec H` hypothesis is
discharged in the unconditional endpoint `actual_digit_recurrence` using
the independent theorem `FullHeight.height_formula`.

## Executable algorithm and exact interpretation

`evaluate n` returns the initial state at zero. At a positive index it
recursively evaluates `n/2`, then applies `evenStep` or `oddStep` according to
the final binary digit. Termination is proved from `n/2<n`.

`evaluate_eq_of_formula` proves all ten computed coordinates correct for any
sequence satisfying the closed form; `formula_unique` proves that there is
only one such sequence. `evaluate_actual_height` identifies the computed
`L` coordinate with `FullHeight.height n`. Finally, `evaluate_isMaximum`
identifies its natural-number value with an attained maximum in
`FiniteEditStability.IsMaximumPrefix`, which quantifies actual finite
`BinaryAvoidance.Edge` paths.

There is one recursive call per binary digit. The module supplies a
ten-coordinate integer linear representation; it does not claim that these
unbounded integer states form a finite automaton, prove that dimension ten is
minimal, or provide a separate bit-complexity theorem.

The original fitted candidate is recorded in
`research/thue-morse/FULL-HEIGHT-CONJECTURE.md`; the proof above, rather than
that packet's numerical evidence, certifies the recurrence. The underlying
population construction is from the pinned September 2026 classification
manuscript cited by `BinaryAvoidance.lean`. No wider-literature novelty claim
is made here.

## Verification

With `ELAN_HOME=C:/Users/Owner/.elan`, from the repository root:

```text
lake env lean lean/SamuelAlexanderResearch/DigitRecurrence.lean
lake build SamuelAlexanderResearch.DigitRecurrence
```

Both checks pass. Selected intermediate and unconditional endpoints print
only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.
The module contains no `sorry`, `admit`, custom `axiom`, or `native_decide`.
