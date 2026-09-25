# The complete Thue–Morse matching-height formula

**Status: the complete closed form is proved in Lean.**
`lean/SamuelAlexanderResearch/FullHeight.lean` proves the candidate formula at
every natural starting vertex, for the actual recursively defined binary
digit-parity sequence and the actual population edges. The finite digit
recurrence is proved separately in `DigitRecurrence.lean`, using this theorem
as its graph-to-formula bridge. No correction to the candidate table was
needed. Its exceptional even case at dyadic scale two is essential.

The finite experiments in `research/thue-morse/FULL-HEIGHT-CONJECTURE.md` were
discovery evidence. The present proof does not use a finite scan, fitted
transition identities, or a postulated formula as a premise. The small
`full-height-structure.py` experiment records the run-pattern discovery only.

The target-dependent binary population is the construction in the pinned
[September 2026 classification manuscript, Section 2](https://raw.githubusercontent.com/avg-netizen/biological-unavoidability/3d6175e3e23f67bd68e7be591b5a9a6d04e496a3/paper.md).
The candidate height table and digit-state representation were supplied by the
parallel source-side investigation and recorded in the conjecture packet.
This note supplies the universal trajectory proof and its formal model bridge;
it makes no literature-priority claim.

## Exact statement and formal endpoints

Write `t(n)` for the parity of the number of ones in the binary expansion of
`n`. The graph has, for every `w ≥ 2`, the edge `w−1 → w` with label `t(w)` and
the edge `w−2 → w` with label `1−t(w)`. There is no edge `0 → 1`. A matching path
uses label `t(k)` on its edge numbered `k`, starting with `k=0`. Its length is
its number of edges.

Let `L(v)` be the attained maximum of all finite matching-path lengths from
`v`. The formal definition is `FullHeight.height`; the theorem
`height_isMaximum` proves `FiniteEditStability.IsMaximumPrefix t v (height v)`.
This predicate includes both an actual path function attaining the stated
length and a bound on every other actual finite matching path from that
start. The definition uses the previously checked existence theorem; the
closed-form theorem supplies its exact value. Start zero is included and has
maximum one.

For a given start `v`, put `n=⌊v/2⌋` and factor

```math
n+1=(2h+1)2^r,
\qquad q=2^r,\quad T=t(h),\quad U=t(h+1).
```

Define `A(h)` to be one precisely when

```math
h\equiv1\pmod4,\qquad t(\lfloor h/4\rfloor)=0,
\qquad t(\lfloor h/4\rfloor+1)=1.
```

Then the exact maximum is:

| Start | Condition | `L(v)` |
|---|---|---|
| even | `T=1` | `1−(r mod 2)` |
| even | `T=0`, `q=2` | `7−2U` |
| even | `T=0`, `q≠2` | `(4−2U)q−1` |
| odd | `T=0` | `0` |
| odd | `T=1`, `U=0` | `4q−1` |
| odd | `T=U=1`, `A(h)=0` | `10q−1` |
| odd | `A(h)=1` | `16q−3` |

The final condition implies `T=U=1`. Boolean bits in arithmetic expressions
mean the natural numbers zero and one. The explicit all-start endpoints are:

```lean
FullHeight.height_formula : FullHeight.FormulaSpec FullHeight.height

FullHeight.height_from_factorization (v h r : Nat)
    (hf : v / 2 + 1 = (2*h+1)*2^r) :
  FullHeight.height v =
    if v % 2 = 0 then FullHeight.evenValue h r
    else FullHeight.oddValue h r

FullHeight.height_closed_form (v : Nat) :
  ∃ h r, v / 2 + 1 = (2*h+1)*2^r ∧
    FullHeight.height v =
      if v % 2 = 0 then FullHeight.evenValue h r
      else FullHeight.oddValue h r
```

`height_closed_form` proves existence of the factorization for every `v`, so
the indexed table is not a theorem about an assumed subset of starts.
`maximum_iff_height` identifies any actual maximum with the displayed value.
The exceptional scale check in `evenValue` is `r=1`, equivalent here to `q=2`.

## Boundary trajectories and the model bridge

For each starting boundary `a`, define

```math
X_a(0)=a,\qquad
X_a(k+1)=
\begin{cases}
X_a(k)+1,&t(X_a(k)+1)=t(k),\\
X_a(k)+2,&t(X_a(k)+1)\ne t(k).
\end{cases}
```

These are boundary trajectories, not asserted matching paths. The existing
interval theorem says that, for `v≥1`, the vertices reached by length-`k`
matching paths from `v` form exactly the half-open interval
`[X_v(k), X_(v+1)(k))`. If the two boundaries are separated at time `K−1` and
equal at time `K`, the maximum length is `K−1`. Coalescence persists forever,
so there is no earlier extinction followed by a reappearance.

`height_eq_of_boundaries` proves this statement for actual path functions. It
uses the interval reachability theorem, extracts an actual prefix at time
`K−1`, and rules out every longer actual prefix by truncating it to time `K`.
Start zero is handled by the already checked direct maximum-one proof,
because the interval theorem requires a positive start.

Two elementary tools organize the proof. A run of ones starting at time `k`
and position `x` has the comparisons `t(x+i+1)=t(k+i)`. A run of twos has the
comparisons `t(x+2i+1)≠t(k+i)`. Existing `run_ones`, `run_twos`, `block_eq`, and
`block_ne` certify these runs. The new `run_ones_last` and `run_twos_last` also
record the position one step before the end.

The new finite-window lemma is equally explicit. If
`t(d+w)=t(w)` throughout `lo≤w<hi`, `lo≤a+1`, and `X_a(K)<hi`, then
`X_(d+a)(k)=d+X_a(k)` for every `k≤K`. Time monotonicity ensures that every bit
queried before time `K` is within the agreed window. This is proved by
induction, with no assumption about colors outside the window.

In the remaining calculations put

```math
z=(4h+2)q.
```

The paired starts are the even start `z−2` and the odd start `z−1`.

## The short cases

The dyadic bit identities give

```math
t(z)=1-T,\qquad t(z+1)=T,\qquad
t(z-1)=(1-T)\mathbin{\mathrm{xor}}(r\bmod2).
```

If `T=0`, the odd-start boundaries `z−1,z` merge at `z+1` after one step,
giving height zero. If `T=1`, the even-start boundaries `z−2,z−1` merge after
one step when `r` is odd and after two steps when `r` is even. Their maxima are
therefore zero and one respectively.

For even starts with `T=0` and `q=1`, the seven row bits immediately above
`4h` are

```math
1,1,0,U,1-U,1-U,U.
```

The first coalescence occurs after two steps if `U=1` and four steps if
`U=0`; hence the height is `3−2U`. The special start zero has this same value.

For `q=2`, `T=0`, `U=1`, colors in the window of length sixteen starting at
`8h` agree with the initial sixteen Thue–Morse colors. Thus the pair at
`8h+2,8h+3` is a translate of the sharp pair at `2,3`; its first coalescence is
at time six and its height is five. The `q=2,U=0` case is included in the
ascent proof below and has height seven.

## The odd `10` case

Suppose `T=1,U=0`. The two complete boundary run patterns are

```math
X_{z-1}:\quad 1^{2q}2^{2q},
\qquad
X_z:\quad 2^q\,1\,2^{q-1}1^{2q}.
```

They meet at time `4q` and position `z+6q−1`. At time `4q−1`, their positions
are respectively `z+6q−3` and `z+6q−2`. Consequently the exact height is
`4q−1`. The run of length `q−1` may be empty, so this proof includes `q=1`.
All comparisons follow by splitting into dyadic blocks with high indices
`4h+2,4h+3`, `2h+2,2h+3`, and `4h+6,4h+7`. Their parities are fixed by
`T=1,U=0`.

## The two odd `11` cases

When `T=U=1`, elementary residue analysis gives

```math
t(h+2)=0,\qquad A(h)=t(h+3).
```

Only residues one and three modulo four are possible. At residue one,
`h=4g+1`, `t(g)=0`, and both sides of the second identity equal `t(g+1)`.
At residue three, the adjacent-one condition forces `t(g+1)=1`, and both
sides are zero. This is `consecutive_ones` in Lean.

If `A(h)=1`, write `h=4g+1` with `t(g)=0,t(g+1)=1`, and put `d=16gq`.
Throughout `0≤w<32q` the colors at `d+w` equal the colors at `w`. The pair at
`z−1,z` is the translate by `d` of the sharp pair at `6q−1,6q`, namely the
already proved equality family at scale `2q`. Its first coalescence is at
time `16q−2`, at reference position `32q−4`, strictly inside the agreed
window. Thus its height is `16q−3`.

Now suppose `A(h)=0`, so `t(h+3)=0`. Put

```math
d=4(h-1)q,\qquad B=(4h+12)q=z+10q.
```

Here `h≥1`. The window `4q≤w<16q` is preserved under translation by `d`,
because its three high-block colors are `t(h),t(h+1),t(h+2)=1,1,0`, exactly
the reference colors `t(1),t(2),t(3)`. The reference trajectories give

```math
X_{z-1}(8q-2)=B-4,\qquad X_z(6q)=B-1.
```

The first identity is the checked sharp upper coalescence. The second comes
from the first `6q` steps of the canonical five-run trajectory, proved as
`canonical_six_join`.

From these states the right boundary makes `4q` ones, ending at time `10q`
and position `B+4q−1`. The left boundary makes

```math
2,2,1,2^{2q-1},
```

also ending at time `10q` and that same position. The two special initial
comparisons use

```math
t(4q-3)=1-t(4q-1),\qquad
t(8q-2)=t(4q-1),\qquad
t(8q-1)=1-t(4q-1).
```

The rest are direct dyadic-block comparisons using `t(h+3)=0`. At time
`10q−1` the left and right positions are `B+4q−3` and `B+4q−2`, so the exact
height is `10q−1`.

## The even `T=0` ascent

It remains to analyze the left boundary from `z−2`. For every `q≥4`, and
also for `q=2,U=0`, its first five steps end at `z+5`. The relevant rows
begin with `1,0,0,1,0,1`; depending on `t(z−1)`, the five advances are
`11221` or `22111`. The hypotheses exclude precisely the exceptional
`q=2,U=1` case already handled above.

The ascent doubles a scale `s=2^m`. Its start and end states are

```math
(5s,z+6s-1)\quad\longrightarrow\quad(10s,z+12s-1),
```

with the run pattern `2^s1^(4s)`. Write `q=Ms` with `M=2^d`. The first run
compares high indices `(2h+1)M+3` and `5`; their bits are one and zero. The
second run compares the four high indices

```math
(4h+2)M+8+j\quad\text{and}\quad6+j,
\qquad0\le j<4.
```

These agree in exactly the ranges needed by the induction:

| Ratio `M=q/s` | Reason for agreement |
|---|---|
| `M≥16` | No carry crosses the `M`-block; the source high bit is `1−T=1`. |
| `M=8` | The carry gives high block `4h+3`, whose bit is `T=0`. |
| `M=4`, `U=0` | The carry gives high block `4h+4`, whose bit is `U=0`. |

Thus the ascent always reaches `s=q/4` when `q≥4`. When `U=0`, one further
doubling reaches `s=q/2`. The case `q=2,U=0` starts at that final scale
`s=1` directly. The universally quantified doubling step is `ascent_step`;
`even_rising` and `even_rising_zero` are the two induction endpoints.

At the final scale, the left boundary makes `3s` twos. Meanwhile the right
boundary from `z−1` has the complete pattern `2^(4s)1^(4s)`. Both end at
time `8s`, at position `z+12s−1`. Immediately before that time their
positions are `z+12s−3` and `z+12s−2`. The required final three high-bit
mismatches and two groups of four high-bit comparisons are proved in
`even_finish` and instantiated for the two cases:

| Condition | Final scale | First coalescence | Height |
|---|---|---|---|
| `U=1`, `q≥4` | `s=q/4` | `2q` | `2q−1` |
| `U=0`, `q≥2` | `s=q/2` | `4q` | `4q−1` |

Together with the short cases, these are exactly all even rows of the table.

## Verification and scope

The module uses Std and the existing checked modules. It has no `sorry`,
`admit`, additional axiom, `native_decide`, or assumed compactness/height
formula. Its few fixed-size base computations use kernel-checked decision
proofs. The selected axiom reports for `height_isMaximum`, `even_rising`,
`odd_nonspecial`, `height_formula`, `height_from_factorization`, and
`height_closed_form` contain only `propext`, `Classical.choice`, and
`Quot.sound`. The direct Lean invocation completed without errors or warnings.

From the repository root, with the pinned Lean toolchain available:

```powershell
lake env lean lean/SamuelAlexanderResearch/FullHeight.lean
```

The independent digit-algebra implementation supplies the executable
fixed-dimensional integer digit recurrence and proves that its output equals this actual
matching height. This note proves no minimality claim for the dimension of
that integer representation. Its mathematical endpoint is the complete
universal matching-height formula, including attainment, all upper bounds,
and start zero.
