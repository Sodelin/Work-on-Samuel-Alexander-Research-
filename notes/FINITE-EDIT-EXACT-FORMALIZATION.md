# Exact finite-edit maxima and the optimal universal additive constant

For a Boolean target `s` agreeing with Thue–Morse `t` at every index `k>=m`,
the new module proves three results:

1. An exact finite-prefix decomposition and an effective attained maximum at
   every start, including zero and early extinction.
2. The entire equality set in the bound `3 L_s(v) <= 8v+8m-1`, for positive
   starts, characterized by a finite test of the edited prefix.
3. The additive integer constant `8m-1` is the smallest one valid uniformly
   over all such edited targets and all positive starts.

The target-dependent graph is always the actual `P_s`. Both its row coloring
and the target word change with `s`.

## Exact prefix decomposition

Let `F_s(v,m)` be the finite list `PhaseHeight.frontier s v m` of reachable
vertices after exactly `m` matching edges. The list is proved equivalent to
actual function-path witnesses, rather than assumed to describe them.

Every `w` in this frontier satisfies

```math
2m\le w,\qquad v+m\le w\le v+2m.
```

The first inequality is the own-target offset invariant. It is what makes
subtracting `2m` safe; in particular the translated suffix cannot introduce
the nonexistent edge `0 -> 1`.

`prefix_decomposition` proves, more generally for any two targets agreeing
from `m` onward,

```math
\operatorname{HasPrefix}(s,v,m+\ell)
\Longleftrightarrow
\exists w\in F_s(v,m),\quad
\operatorname{HasPrefix}(\operatorname{shift}(t,m),w-2m,\ell).
```

The forward direction cuts and translates the actual path. The reverse
direction translates the suffix back and splices it to an actual frontier
witness, with the target labels in their original forward order.

For Thue–Morse, `thue_prefix_decomposition` replaces the suffix predicate by
the checked numerical condition

```math
\ell\le L_m(w-2m),
```

where `L_m` is the exact computable `PhaseHeight.height m`.

## Exact maximum, including early death

If `F_s(v,m)` is nonempty, the actual maximum is

```math
L_s(v)=m+\max_{w\in F_s(v,m)}L_m(w-2m).
```

`maxSuffix_attained` proves that the finite maximum is achieved by a listed
vertex. If the frontier is empty, every match dies strictly before time `m`;
the bounded earlier-prefix algorithm returns the actual maximum.

`FiniteEditExact.height` implements these two cases.
`height_isMaximum`, `maximum_iff_height`, and `hasPrefix_iff_le_height` prove
its exact actual-graph interpretation. `early_extinction` proves the strict
inequality in the empty-frontier case. The cutoff `m=0`, length zero, and
translated start zero are included. No supplied bound on all matches or
choice of a successful continuation is an endpoint hypothesis.

## Complete equality criterion for the universal bound

Define the finite condition

```math
\operatorname{TwoPrefix}(s,v,m)
\quad\Longleftrightarrow\quad
\forall k<m,\ s(k)=1-\operatorname{row}_s(v+2k+2).
```

This says exactly that the explicit path `v,v+2,...,v+2m` matches the first
`m` target bits. It is a finite bit test, not an assumed infinite path or
maximum-length statement.

For `v>=1`, `finite_edit_extremal_iff` proves

```math
\begin{split}
&\operatorname{IsMaximumPrefix}(s,v,L)
  \ \land\ 3L=8v+8m-1\\
&\quad\Longleftrightarrow\quad
\exists n,\quad m\le q=2^n,\quad
v=3q-m-1,\quad L=8q-3,\quad
\operatorname{TwoPrefix}(s,v,m).
\end{split}
```

To prove necessity, transport an extremal edited match to the original
Thue–Morse graph. Saturation forces the new start to equal `v+m`. The two
prefixes meet at time `m`; their displacement bounds then force every
edited prefix step to be a two-step and every original prefix step to be
a one-step. Cutting the edited prefix gives a positive-start shifted match
which saturates the already proved phase bound. The exact shifted equality
theorem supplies `m<=q` and the dyadic locations, including its separate
smallest-scale case.

For sufficiency, the explicit two-step prefix is spliced to the already
checked shifted dyadic extremal family. The universal upper bound proves
that the resulting actual matching length is maximal.

This criterion classifies equality in the universal bound for each fixed
edited target. It does not assert that every edited target attains that
bound.

## Sharp universal constant

For `q=2^n >= m+1`, set `v=3q-m-1` and define

```math
s(k)=
\begin{cases}
1-t(v+2k+2),&k<m,\\
t(k),&k\ge m.
\end{cases}
```

All relevant destinations lie beyond the edited row region. Thus the
displayed edited prefix uses only two-steps, and `sharpEdit_equality` proves
an actual maximum `8q-3` at `v`, with equality in `3L=8v+8m-1`.

`optimal_universal_additive_constant m B`, with `B : Int`, proves

```math
\begin{split}
&\bigl[\forall s\text{ agreeing with }t\text{ from }m,
\ \forall v\ge1,\quad 3L_s(v)\le8v+B\bigr]\\
&\hspace{4em}\Longleftrightarrow\quad 8m-1\le B.
\end{split}
```

The theorem uses actual attained maxima. Integer coefficients retain the
unedited optimum `-1` at `m=0`; natural subtraction is not used to replace it
by zero.

## Remaining distinction

For a particular edited target, its best constant
`B_s = sup_{v>=1}(3 L_s(v)-8v)` may be smaller than `8m-1`. The present
module does not give a finite global classification of that smaller
target-specific optimum or of its maximizing starts. It gives an exact
algorithm for each specified start, the full equality criterion at the
optimal universal allowance, and a proof that the universal allowance is
sharp. A more efficient closed form for all phases is also separate from
the exact finite algorithm used here.

## Verification

With `ELAN_HOME=C:/Users/Owner/.elan`, from the repository root:

```text
lake env lean lean/SamuelAlexanderResearch/FiniteEditExact.lean
lake build SamuelAlexanderResearch.FiniteEditExact
```

Both checks pass. Eight printed endpoints use only `propext`,
`Classical.choice`, and `Quot.sound`. The module contains no `sorry`,
`admit`, custom `axiom`, or `native_decide`.
