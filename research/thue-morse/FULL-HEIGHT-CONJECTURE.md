# A candidate formula for every Thue-Morse matching maximum

**Status: conjecture.** The finite diagnostics below have not proved these
identities for arbitrary indices. The accepted sharp bound and dyadic equality
theorem are separate Lean results. This packet records a concrete next theorem,
not a certified digit algorithm.

The target is binary digit parity `t`. In the manuscript's own graph `P_t`,
the edge to `w>=2` from `w-1` carries `t(w)`, and the edge from `w-2` carries
`1-t(w)`. There is no edge `0 -> 1`. Let `L(v)` count the maximum number of
initial target labels matched from `v`; in particular, `L(0)=1`.

## Candidate closed form

Set `n=floor(v/2)` and write uniquely

`n+1 = 2^r (2h+1)`, with `q=2^r`, `T=t(h)`, and `U=t(h+1)`.

Let `A(h)=1` exactly when `h=1 (mod 4)`, `t(floor(h/4))=0`, and
`t(floor(h/4)+1)=1`.

| Start parity | Condition | Candidate `L(v)` |
|---|---|---|
| even | `T=1` | `1-(r mod 2)` |
| even | `T=0`, `q=2` | `7-2U` |
| even | `T=0`, `q!=2` | `(4-2U)q-1` |
| odd | `T=0` | `0` |
| odd | `T=1`, `U=0` | `4q-1` |
| odd | `T=1`, `U=1`, `A(h)=0` | `10q-1` |
| odd | `A(h)=1` | `16q-3` |

The last condition implies `T=U=1`, so these cases are disjoint and exhaustive.
The exceptional `q=2` even case is necessary.

## Candidate integer recurrence

At index `n`, define coordinates

`(1,T,U,V,L,E,O,X,F,C)`

by `T=t(n)`, `U=t(n+1)`, `V=TU`, `L=L(n)`, `E=L(2n)`, `O=L(2n+1)`,
`X=(L(4n+1)-t(n))/2`, `F=L(4n+2)`, `C=L(4n+3)`.
The candidate initial vector is `(1,0,1,0,1,1,0,0,5,0)`.

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

A proof must establish that `X` is integral and that the displayed coordinates
are the actual graph maxima, then prove every transition universally. A
finite transition system for a fitted sequence does not accomplish that.

## Evidence and falsification

The side research task fitted a rational kernel basis from ten indices;
two modular rank experiments stabilized at dimension ten through depth nine.
Those exploratory reports suggested the integer recurrence and then this
closed form. They are evidence about sampled data.

The independent integration checker
[kernel_conjecture_check.py](kernel_conjecture_check.py) compares the formula
with the stored exact 131,071 positive-start values, checks start zero directly,
checks 16,384 full coordinate transitions, and runs fresh bounded frontier
computations using a fixed seed. It includes deliberately long cases and
lists every case that reaches the cap. See the exact
[machine-readable result](kernel-conjecture-results.json).

```sh
python research/thue-morse/kernel_conjecture_check.py \
  --output research/thue-morse/kernel-conjecture-results.json
```

## Proof route and priority boundary

Write `v=(4h+2)q-1` or `v=(4h+2)q-2`. Decompose the actual row colors into
dyadic `q`-blocks and classify the finite high-bit patterns responsible for
the candidate extinction times. The existing exact interval theorem and
dyadic run lemmas can support this proof. Failed induction or a single
counterexample should revise the formula rather than be hidden by a cutoff.

The framework of regular sequences is established: Allouche and Shallit,
[The Ring of k-Regular Sequences](https://doi.org/10.1016/0304-3975(92)90001-V)
(1992), and [its sequel](https://doi.org/10.1016/S0304-3975(03)00090-2) (2003).
The proposed contribution is the particular matching-height formula and its
graph proof; no global novelty claim has been established.
