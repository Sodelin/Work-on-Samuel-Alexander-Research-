# Full matching height: current proof status

Status checked on 25 September 2026, after the public PR 5 release. This addendum updates the current research packet. Earlier reports remain dated records of what was established at their release.

**The implementation owner reports that the full Thue–Morse height formula and its unconditional binary-digit evaluator now compile. This review independently checked the source statements and file hashes. The combined axiom audit, final release tree and CI are still pending.** These results must therefore not yet be described as part of the public PR 5 release.

## What has changed

The earlier audit asked for coupled functions, proved even/odd transitions, initial conditions, and a proof that the resulting calculation measures the actual graph quantity. The current source now supplies that connection. Its final statements do not assume the proposed formula.

Let $`H(v)`$ be the maximum number of consecutive target labels matched by a path beginning at vertex $`v`$ in the actual Thue–Morse population, with the Thue–Morse word itself as target. Length counts edges, and length zero is allowed. `FullHeight.height_isMaximum` proves both attainment and an upper bound on every such finite matching path. The function is consequently more than a numerical estimate or a maximum observed in a finite search.

| Source endpoint | What the statement establishes |
| --- | --- |
| `FullHeight.height_isMaximum` | The graph has a path attaining the stated height, and every matching path has length at most that height. |
| `FullHeight.height_formula` | The actual height satisfies the complete proposed formula. |
| `FullHeight.height_from_factorization` | Any valid odd-times-power-of-two factorization evaluates the height. |
| `FullHeight.height_closed_form` | Every natural starting vertex has such a factorization and is covered, including zero. |
| `DigitRecurrence.actual_digit_recurrence` | The actual height and nine auxiliary integer coordinates satisfy the initial condition and both binary transitions. |
| `DigitRecurrence.evaluate_actual_height` | The executable evaluator's height coordinate equals the actual graph height. |
| `DigitRecurrence.evaluate_isMaximum` | The computed height is an attained maximum of actual matching paths, with no formula premise. |

## The formula in readable notation

Write $`t(n)\in\{0,1\}`$ for the Thue–Morse bit, with the Boolean values in Lean interpreted as zero and one. Define a predicate $`S(h)`$ by

```math
S(h)\iff h\equiv1\pmod4
\quad\text{and}\quad
t(\lfloor h/4\rfloor)=0
\quad\text{and}\quad
t(\lfloor h/4\rfloor+1)=1.
```

For nonnegative integers $`h,r`$, define

```math
E(h,r)=
\begin{cases}
1-(r\bmod2), & t(h)=1,\\
7-2t(h+1), & t(h)=0\ \text{and}\ r=1,\\
\bigl(4-2t(h+1)\bigr)2^r-1,
  & t(h)=0\ \text{and}\ r\ne1,
\end{cases}
```

and

```math
O(h,r)=
\begin{cases}
0, & t(h)=0,\\
4\cdot2^r-1, & t(h)=1\ \text{and}\ t(h+1)=0,\\
16\cdot2^r-3, & t(h)=t(h+1)=1\ \text{and}\ S(h),\\
10\cdot2^r-1, & t(h)=t(h+1)=1\ \text{and}\ \neg S(h).
\end{cases}
```

The proved identities are

```math
H\bigl((4h+2)2^r-2\bigr)=E(h,r),
\qquad
H\bigl((4h+2)2^r-1\bigr)=O(h,r).
```

To apply the formula to any starting vertex, factor

```math
\left\lfloor\frac v2\right\rfloor+1=(2h+1)2^r.
```

Then use $`E(h,r)`$ when $`v`$ is even, and $`O(h,r)`$ when $`v`$ is odd. The argument on the left is always positive, so every natural vertex is covered. For orientation, substitution gives the following values; this small table illustrates the formula and is not the proof of it.

| Starting vertex | Maximum matching length |
| --- | --- |
| 0 | 1 |
| 1 | 0 |
| 2 | 5 |
| 5 | 13 |
| 11 | 29 |

## What the binary recurrence means

The executable `evaluate` function repeatedly divides the input by two, then applies the transition for the removed binary digit as recursion unwinds. Its state has ten integer coordinates. One coordinate stores the constant one; others store Thue–Morse bits, their product, height values at related indices, and an auxiliary integer expression. Both transitions are integer linear combinations of these coordinates.

The number of coordinates is fixed, while their values can grow. **This is not a claim that the entire state space is finite, nor a proof that the height sequence is automatic.** No minimal-dimension theorem is claimed. The evaluator takes one recursive transition per binary digit; the source reviewed here does not establish a machine-level running-time bound for arithmetic on growing integers.

The final evaluator theorem is unconditional about the actual maximum. Earlier helper theorems still take a `FormulaSpec` hypothesis because they are reusable results for any function satisfying that specification. The endpoint applies them to `FullHeight.height_formula`, which supplies the proved specification for the graph height.

## Remaining distinctions

- **Literal library formulation of regularity:** the implementation owner is separately adding the Mathlib theorem that the integer module generated by the binary kernel is finitely generated. The reviewed recurrence is the substantive ingredient, but this packet does not yet record that separate library endpoint as audited.
- **Literature priority:** a proved formula and a proved recurrence do not establish that the result is absent from the literature. The earlier Allouche–Shallit and synchronized-sequence source comparison remains relevant. This addendum makes no claim of a first discovery or a first formalization.
- **Other targets and graphs:** this complete formula concerns the Thue–Morse word in its own target-dependent population. It is not a formula for every automatic target, every biological population, or every specieslike cluster.
- **Release verification:** the implementation owner reported a growing aggregate of 47 core modules and 361 selected endpoints. These are provisional integration counts, not a completed independent audit or a public CI receipt.

The earlier sentence that a stable-looking rank of finite tables is only a conjecture generator remains correct. The current work advances beyond that stage by proving the identities and their connection to the graph. The historical audit has therefore been preserved and linked to this status update rather than rewritten as though these proofs existed at its release.

## Evidence inspected

This review read the definitions of the actual maximum and both formula branches; the all-vertex factorization proof; the ten-coordinate state and transitions; the terminating evaluator; and its final unconditional theorems. A second reader independently confirmed the endpoint scope, including the absence of a caller-supplied formula premise. That reader also checked that the final conversion from integers to natural numbers cannot hide a negative output: the preceding theorem identifies the output with the actual natural-number height. The implementation owner retains responsibility for the combined build and axiom audit.

| Local source inspected | SHA-256 |
| --- | --- |
| `FullHeight.lean` | `b120919c7861603401be5d88c29c184068c971cf7e98f8f2fc339312f224a464` |
| `DigitRecurrence.lean` | `73ca15003264178d04284508c61d6eba358b397e57830acb798c9f1186114637` |

Source checkout: `C:/Users/Owner/Documents/Codex/2026-09-24/alexander-formalization`. These are source-byte hashes, not commit identifiers. No new publication was performed for this status update.

See the [current follow-up index](RESEARCH-FOLLOWUP-INDEX.md), the [earlier finite-edit and cap-three audit](FINITE-EDIT-AND-CAP-THREE-AUDIT.md), and the [PR 5 release receipt](FINAL-RELEASE-RECEIPT.md).
