# Sharp bound proof by explicit boundary trajectories

**Status:** independently reviewed prose proof and complete Lean proof of
the sharp bound, finite maxima, equality family, and exact equality set.
[`ThueMorseBits.lean`](../../lean/SamuelAlexanderResearch/ThueMorseBits.lean)
defines the actual bit sequence and proves its identities;
[`SharpThueMorse.lean`](../../lean/SamuelAlexanderResearch/SharpThueMorse.lean)
checks all dyadic runs and connects the result to the original edges.
The [final audit](../../verification/formal-audit.json) passes all 80
selected endpoints across eleven modules. The exact baseline `H(v)`
first-hit formula and real-coefficient optimality below remain prose
corollaries, not separately exported Lean theorems. Earlier receipts
preserve the historical stages before this complete formalization.

## Exact statement

Write `t(n)=popcount(n) mod 2`. For each integer `w>=2`, the population has
edges `w-1 -> w` labelled `t(w)` and `w-2 -> w` labelled `1-t(w)`; there is
no edge `0 -> 1`. A matching path starting at `v` has its edge at index `k`
labelled `t(k)`, beginning with `k=0`. Let `L(v)` be its maximum length.

The theorem is:

1. Every `v>=1` has finite `L(v)` and `3 L(v)<=8v-1`.
2. For every integer `n>=0`,
   `L(3*2^n-1)=8*2^n-3`.
3. Equality in `3 L(v)<=8v-1` occurs exactly when
   `v=3*2^n-1` for an integer `n>=0`.

## Boundary trajectories and the baseline

Use the exact interval theorem in
[`INTERVAL-REDUCTION.md`](INTERVAL-REDUCTION.md) and the Lean module
[`ThueMorseBound.lean`](../../lean/SamuelAlexanderResearch/ThueMorseBound.lean).
Define

    f_b(x) = x+1 if t(x+1)=b, and x+2 otherwise;
    X_0(v) = v;
    X_(k+1)(v) = f_(t(k))(X_k(v)).

For every `v>=1`, the complete matching frontier at depth `k` is

    [X_k(v), X_k(v+1)).

Each `f_b` is nondecreasing. Hence `X_k(u)<=X_k(v)` whenever `u<=v`.
Equality of two trajectories persists at all later times. These auxiliary
trajectories need not themselves be matching paths: an advance of 2 is
defined by the mismatch at the next vertex, regardless of the label on the
two-step edge. All conclusions about matching paths use the interval
theorem, not an assumption that an auxiliary trajectory is a path.

The elementary identity `t(2k+1)=1-t(k)` gives

    X_k(0)=2k

by induction. Call this the baseline. Monotonicity gives `X_k(v)>=2k` for
every `v>=0`. Once a trajectory meets the baseline it remains there.

We repeatedly use the following binary-block identity. If `r` is a power
of two and `0<=i<r`, then

    t(ar+i) = t(a) XOR t(i).

This follows because the binary digits of `ar` and `i` occupy disjoint
positions. No overlap-freeness theorem is used in this proof.

## Lemma 1: the common dyadic descent

Fix a power of two `q>=1` and put `T=8q`. Suppose that at time `4q` a
boundary trajectory is at vertex `10q-1`. It then satisfies

    X_(T-3)=2(T-3)+1,
    X_(T-2)=2(T-2).

**Proof.** For each `r=q,q/2,...,1`, consider the state

    time k = T-4r,
    vertex x = 2T-6r-1.

This is the assumed initial state when `r=q`. We show that the next `r`
advances are all 2 and the following `r` advances are all 1.

Write `M=T/r=2^s`, where `s>=3`. In the first run, for `0<=i<r`, the target
and the inspected source vertex have bits

    target: t((M-4)r+i),
    source: t(x+2i+1)
          = t(2((M-3)r+i))
          = t((M-3)r+i).

Since `M-4` is even, `t(M-3)=1-t(M-4)`. The binary-block identity says that
the displayed bits are opposite. Thus the advance is 2 at every step in
this run. At its end the time and vertex are `T-3r` and `2T-4r-1`.

In the second run, for `0<=j<r`, the inspected source bit and target bit
are respectively

    t((2M-4)r+j),
    t((M-3)r+j).

Now `t(2M-4)=t(M-2)=t(M-3)`: for `M=2^s`, both `M-2` and `M-3` have
exactly `s-1` binary ones. The block identity therefore makes these bits
equal, so every advance is 1. The end state is

    time T-2r,
    vertex 2T-3r-1,
    offset above the baseline r-1.

For `r>1` this is exactly the required initial state with `r` replaced by
`r/2`. For `r=1`, the first advance goes from time `T-4`, offset 1, to time
`T-3`, still offset 1; the second reaches offset 0 at time `T-2`. This
proves both displayed conclusions. QED.

## Lemma 2: an upper trajectory reaches the descent state

For every power of two `q>=1`,

    X_(4q)(6q-1)=10q-1,
    X_(8q-2)(6q-1)=2(8q-2).

**Proof.** Starting from `6q-1`, the first `4q` advances are all 1. Indeed,
at step `0<=i<4q`, this proposed run compares `t(6q+i)` with `t(i)`. The
four high-block indices for the former are `6,7,8,9`, with parities
`0,1,1,0`; those for the latter are `0,1,2,3`, with the same parities.
The binary-block identity proves equality throughout the run. Its end
vertex is `(6q-1)+4q=10q-1`. Lemma 1 then proves the second assertion. QED.

## Lemma 3: the lower trajectory joins the same descent state

For every power of two `q>=1`,

    X_(4q)(3q)=10q-1.

**Proof.** If `q=1`, the vertices through time 4 are

    3, 5, 7, 8, 9,

with advances `2,2,1,1`, directly from the target bits `0,1,1,0`.

Otherwise write `q=2r`, with `r` a power of two. The exact sequence of
advances is the following five runs; the third run is empty when `r=1`.

| Run | Start time | Start vertex | Advance | Number of advances | End time | End vertex |
|---|---:|---:|---:|---:|---:|---:|
| I | `0` | `6r` | `2` | `2r` | `2r` | `10r` |
| II | `2r` | `10r` | `1` | `1` | `2r+1` | `10r+1` |
| III | `2r+1` | `10r+1` | `2` | `r-1` | `3r` | `12r-1` |
| IV | `3r` | `12r-1` | `1` | `2r` | `5r` | `14r-1` |
| V | `5r` | `14r-1` | `2` | `3r` | `8r` | `20r-1` |

We verify each run under the defining boundary rule.

**Run I.** For `0<=i<2r`, the inspected source bit is
`t(6r+2i+1)=1-t(3r+i)`, while the target bit is `t(i)`.
For the two length-`r` blocks, the high indices `3,4` have parities `0,1`,
the same as `0,1`. Hence `t(3r+i)=t(i)`, so every comparison is a mismatch
and every advance is 2.

**Run II.** The target bit is `t(2r)=1`, and the inspected source bit is
`t(10r+1)=1`. For `r=1`, the latter is `t(11)=1`. For `r>=2`, the block
identity gives `t(10r+1)=t(10) XOR t(1)=0 XOR 1=1`. Thus this advance is 1.

**Run III.** For `0<=i<r-1`, put `j=1+i`, so `1<=j<r`. The source bit is

    t(10r+2+2i) = t(5r+j) = t(j),

whereas the target bit is `t(2r+j)=1-t(j)`. Thus the advances are 2. When
`r=1` there is no index in this run, as required by the table.

**Run IV.** For `0<=i<2r`, the source and target bits are `t(12r+i)` and
`t(3r+i)`. The high-block pairs `12,13` and `3,4` both have parities `0,1`,
so these bits agree and every advance is 1.

**Run V.** For `0<=i<3r`, the source bit is
`t(14r+2i)=t(7r+i)`, while the target bit is `t(5r+i)`. The high-block
triples `7,8,9` and `5,6,7` have respectively parities `1,1,0` and `0,0,1`.
They are complementary throughout, so every advance is 2.

The end state is therefore time `8r=4q`, vertex `20r-1=10q-1`, as claimed.
QED.

## The global sharp inequality

For `v=1`, both possible outgoing edges have label 1, whereas the first
target bit is `t(0)=0`. Thus `L(1)=0`, satisfying the inequality.

For any integer `v>=2`, choose the power of two `q` such that

    3q <= v+1 < 6q.

Such a `q` exists by taking the largest dyadic `q` with `3q<=v+1`.
Since the quantities are integers, `v+1<=6q-1`. At time `K=8q-2`,
monotonicity, the baseline identity, and Lemma 2 give

    2K = X_K(0)
       <= X_K(v)
       <= X_K(v+1)
       <= X_K(6q-1)
       = 2K.

Both frontier boundaries coincide, so the interval theorem proves
finiteness and `L(v)<=K-1=8q-3`. Moreover `v>=3q-1`, and consequently

    3L(v) <= 24q-9 <= 8v-1.

This proves the claimed bound for every `v>=1`.

## The equality family

Fix a power of two `q>=1`, put `v=3q-1`, and set `T=8q`.
By Lemmas 1 and 3, the upper frontier boundary satisfies

    X_(T-3)(v+1) = 2(T-3)+1,
    X_(T-2)(v+1) = 2(T-2).

The lower boundary `X_k(v)` has already met the baseline by time `T-3`.
For `q>=2`, apply Lemma 2 with power of two `q/2`: its starting vertex
`6(q/2)-1` is exactly `v`, and it reaches the baseline at time
`8(q/2)-2=4q-2`, which is at most `T-3`. For `q=1`, the trajectory from
`v=2` is `2,3,4` through time 2 and so also meets the baseline before
`T-3=5`.

Thus the frontier at depth `T-3` is exactly

    [2(T-3), 2(T-3)+1),

a nonempty singleton, and the frontier at depth `T-2` is empty. The exact
maximum-length characterization proves

    L(3q-1)=T-3=8q-3.

Substituting `q=2^n` gives the requested equality for every integer `n>=0`.

## Exact equality cases and optimality

For every `v>=2`, the global proof chose a dyadic `q` with
`3q-1<=v<=6q-2` and proved

    3L(v) <= 24q-9 <= 8v-1.

If `v>3q-1`, the second inequality is strict. Hence equality can only occur
at `v=3q-1`, and the preceding section proves that it does occur at every
such vertex. At `v=1` the inequality is also strict. This establishes the
complete equality classification.

The following real-coefficient optimality statement is a prose corollary
of the checked equality family. Along that family,

    L(3q-1)/(3q-1) = (8q-3)/(3q-1) -> 8/3

as dyadic `q` tends to infinity. Therefore `8/3` is the optimal leading
coefficient: no inequality `L(v)<=c v+C` with fixed `c<8/3` and fixed
finite `C` can hold for all starts. For coefficient `8/3`, the additive
term `-1/3` in the displayed global bound is also attained by every member
of the equality family.

## Stronger first-hit invariant: prose corollary

The trajectory meeting time of the baseline has an exact step-function
formula. Define `H(v)` as the first `k>=0` with `X_k(v)=2k`. Then

    H(0)=0,
    H(1)=H(2)=2,
    H(v)=8q-2 for 3q<=v<=6q-1, where q is a power of two.

The last assertion follows without further trajectory analysis: Lemmas 1
and 3 put the trajectory from `3q` strictly above the baseline at time
`8q-3`, while Lemma 2 puts the trajectory from `6q-1` on the baseline at
time `8q-2`. Monotonicity sandwiches every intermediate start between
these two trajectories. Since meeting the baseline is permanent, these
two facts identify the first meeting time. The values for starts 1 and 2
follow directly from their first two advances.

This exact invariant is stronger than needed for the global inequality.
It also explains why the equality family occurs at dyadic jumps in the
baseline meeting time, despite irregular small values of `L(v)` elsewhere.

## Evidence boundaries and source audit

The generic interval theorem is checked in `ThueMorseBound.lean`; the
actual bit identities are checked in `ThueMorseBits.lean`; and the run
formulas and sharp conclusions are checked in `SharpThueMorse.lean`.
The exported endpoints include `sharp_path_bound`, `sharp_maximum_exists`,
`sharp_equality_family`, and `sharp_equality_indices`. The original graph
is connected by `binary_edge_iff`, `binary_prefix_reachable`, and
`binary_path_prefix_bound`. The complete library builds, and all 80
selected endpoints depend only on subsets of `propext`, `Classical.choice`,
and `Quot.sound`, as recorded with final source hashes in the linked audit.
The exact `H(v)` first-hit formula and real-coefficient optimality remain
prose corollaries despite their checked component lemmas.

A second agent independently rederived the descent comparisons and the
five-run calculation, checked the `r=1` and `q=1` cases and the `K-1`
extinction indexing, and found no gap or off-by-one error. The coordinating
agent also reviewed and accepted the algebra and boundary argument. This
is independent agent review, not a claim of external mathematical peer
review.

The reproducible diagnostic is
`python research/thue-morse/sharp_check.py --output research/thue-morse/sharp-check-results.json`
from the repository root. It passes 18 complete trajectories at exponents
`0<=n<=8`, 8,140 advance comparisons, and 256 bounded `H(v)` checks, and
compares the inequality and exact equality set with the existing scan.
The independent reviewer also replayed all phases and first-hit times
through `n=14`. These finite checks test transcription and indexing; the
universal claims rest on the proof and Lean verification.

This argument uses only the binary-digit definition of `t`, the proved
interval theorem, monotonicity, and finite algebraic block identities with
arbitrary dyadic scale. Finite scans are unnecessary for its universal
steps. In particular it does not invoke the overlap-freeness premise used
by the older quadratic proof. The primary structural source remains
Berstel and Seebold,
[*A characterization of overlap-free morphisms*, Discrete Applied
Mathematics 46 (1993), 275-281](https://doi.org/10.1016/0166-218X(93)90107-Y),
already audited in the preceding note. That source contextualizes the
classical Thue-Morse morphism; no theorem from it is an additional premise
of this new trajectory argument. No literature-priority claim is made.
