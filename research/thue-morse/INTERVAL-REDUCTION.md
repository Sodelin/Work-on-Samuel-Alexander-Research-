# Exact interval and coalescence reduction

**Result:** a universal structural reduction, proved below and checked in Lean.
**Scope:** this generic reduction alone does not prove a numerical bound.
The subsequent [explicit trajectory proof](NEXT-INVARIANT.md) resolves both
sharp claims, with the Thue-Morse-specific Lean results in
[`SharpThueMorse.lean`](../../lean/SamuelAlexanderResearch/SharpThueMorse.lean).

## Population and statement

Let $\operatorname{color}:\mathbb{N}\to\{0,1\}$ be any binary vertex coloring and let $b_0,b_1,\ldots$ be any
binary target word. For every $w\ge 2$, the incoming edges are $w-1 \to w$ with
label $\operatorname{color}(w)$, and $w-2 \to w$ with label $1-\operatorname{color}(w)$. There is no edge $0 \to 1$.
Start at an integer $v\ge 1$; the first matched edge has target label $b_0$.

For each bit $b$, define the deterministic map

$$
f_b(x)=\begin{cases}x+1,&\operatorname{color}(x+1)=b,\\x+2,&\text{otherwise}.\end{cases}
$$

Define $A_0=v$, $C_0=v+1$, and

$$
\begin{aligned}
A_{k+1}&=f_{b_k}(A_k),\\
C_{k+1}&=f_{b_k}(C_k).
\end{aligned}
$$

**Theorem.** For every $k\ge 0$, the complete set of endpoints of matching paths
of length $k$ from $v$ is the half-open integer interval $[A_k,C_k)$. This
includes the empty case $A_k=C_k$. The maps $f_b$ are nondecreasing, so
$A_k\le C_k$ for all $k$; equality persists once it occurs.

Consequently, if $L(v)$ is finite, its exact characterization is

$$
\begin{aligned}
A_{L(v)}&<C_{L(v)},\\
A_{L(v)+1}&=C_{L(v)+1}.
\end{aligned}
$$

Equivalently, $L(v)$ is one less than the first coalescence index. The empty
frontier at depth $k+1$ means that length $k$ is the maximum; this shift is
essential, for example $L(1)=0$ and $L(2)=5$ in the Thue-Morse instance.

## Proof

First, $x+1 \le f_b(x) \le x+2$. If $x<y$, then
$f_b(x)\le x+2\le y+1\le f_b(y)$; equality of inputs is immediate. Thus $f_b$ is
nondecreasing.

Suppose the current frontier is $[a,c)$, where $1\le a\le c$. If $a=c$, its
successor frontier is empty and $[f_b(a),f_b(c))$ is empty as well. Assume
$a<c$. A candidate successor lies between $a+1$ and $c+1$, inclusively.
Every integer $w$ with $a+2\le w\le c$ has both predecessors $w-1$ and $w-2$ in
the frontier. Their two incoming labels are complementary, so exactly one
matches $b$; hence every such interior successor is reachable. At the lower
boundary, $a+1$ has only predecessor $a$ in the frontier and is included
exactly when $\operatorname{color}(a+1)=b$. At the upper boundary, $c+1$ has only predecessor
$c-1$ in the frontier and is included exactly when $\operatorname{color}(c+1)\ne b$.

These conditions say precisely that the new frontier is
$[f_b(a),f_b(c))$. They also cover a singleton input: the interior range is
empty, and the two boundary candidates determine the result. Because
$a\ge 1$, every candidate successor is at least 2; the omitted $0 \to 1$ edge
is respected. Induction from the singleton $[v,v+1)$ proves the theorem.
Once the boundary values coincide, applying the same next map keeps them
equal, proving persistence of extinction. QED.

## Specialization and an exact dyadic recurrence

For the research challenge set $\operatorname{color}(n)=b_n=t(n)$, where
$t(n)=\operatorname{popcount}(n) \bmod 2$. The elementary identities

$$
t(2m)=t(m),\qquad t(2m+1)=1-t(m)
$$

follow directly from appending a binary digit. Thus consecutive target bits
at indices $2j,2j+1$ are $b,1-b$, with $b=t(j)$. Put
$H_b=f_{1-b}\circ f_b$. For all $m\ge 0$:

| Input | Condition | Output of $H_b$ |
|---|---|---|
| $2m$ | $t(m+1)=b$ | $2m+3$ |
| $2m$ | $t(m+1)\ne b$ and $t(m)=b$ | $2m+4$ |
| $2m$ | $t(m+1)\ne b$ and $t(m)\ne b$ | $2m+2$ |
| $2m+1$ | $t(m+1)=b$ | $2m+3$ |
| $2m+1$ | $t(m+1)\ne b$ and $t(m+2)=b$ | $2m+5$ |
| $2m+1$ | $t(m+1)\ne b$ and $t(m+2)\ne b$ | $2m+4$ |

Here is a direct verification, independent of the diagnostic computation.
For even input, if $t(m)\ne b$, the first map sends $2m$ to $2m+1$; the second
map sends this to $2m+2$ when $t(m+1)\ne b$, and to $2m+3$ otherwise. If
$t(m)=b$, the first map sends $2m$ to $2m+2$; the second sends this to
$2m+3$ when $t(m+1)=b$, and to $2m+4$ otherwise. These are exactly the first
three rows. For odd input, when $t(m+1)=b$ the two maps successively reach
$2m+2$ and $2m+3$. Otherwise the first reaches $2m+3$, and the second reaches
$2m+4$ when $t(m+2)\ne b$, or $2m+5$ when $t(m+2)=b$. This proves the last
three rows.

Therefore the trajectory at even times can be computed exactly by

$$
X_{2j+2}=H_{t(j)}(X_{2j}).
$$

This table is a proved substitution reduction, but does not by itself give
an induction for the sharp constant: the even and odd cases retain
different neighboring half-scale bits. The subsequent proof controls
the meeting time using explicit dyadic blocks of boundary advances.
In precise terms, the sharp global bound is equivalent to coalescence by

$$
K(v)=\left\lfloor\frac{8v-1}{3}\right\rfloor+1,
$$

for every $v\ge 1$. The equality formula requires separation at
$k=8\cdot 2^n-3$ and coalescence at $k+1$, starting from $3\cdot 2^n-1$ and $3\cdot 2^n$.
The subsequent [dyadic trajectory proof](NEXT-INVARIANT.md) and
[`SharpThueMorse.lean`](../../lean/SamuelAlexanderResearch/SharpThueMorse.lean)
prove these infinite claims and the exact equality set. The full $H(v)$
first-hit formula and real-coefficient optimality now have separate checked endpoints in SharpCorollaries and RealBridges.

## Lean scope and verification

The independent module is
`lean/SamuelAlexanderResearch/ThueMorseBound.lean`, importing only `Std`.
It defines the actual incoming-edge relation with $2\le w$, using inequality
of Boolean bits for the complementary label. It proves:

- `interval_step`: exact one-step image of an interval for arbitrary binary
  coloring and target bit.
- `reachable_iff_interval`: exact frontiers for all lengths, including empty
  frontiers, from every $v\ge 1$ and arbitrary target word.
- `coalescence_persists`: equality of two trajectories at one depth implies
  equality at every later depth.
- `maximum_length_iff`: maximum matching length is strict separation at that
  depth and coalescence at the following depth.

This particular Lean module is generic; it has no Thue-Morse-specific
premise. The displayed two-step table has the elementary prose proof above.
The full sharp theorem is checked separately in `SharpThueMorse.lean`,
using actual bits from `ThueMorseBits.lean`, complete dyadic run proofs,
the original-edge bridge, and the exact equality classification. Cite
that module for the numerical bound; the generic interval module alone
does not establish it.

From the repository root, in PowerShell:

```powershell
$env:ELAN_HOME = 'C:\Users\Owner\.elan'
& 'C:\Users\Owner\.elan\bin\lean.exe' --version
& 'C:\Users\Owner\.elan\bin\lean.exe' 'lean\SamuelAlexanderResearch\ThueMorseBound.lean'
python research/thue-morse/interval_check.py --output research/thue-morse/check-results.json
lake build
python checks/audit_lean.py --output verification/formal-audit.json
python research/thue-morse/sharp_check.py --output research/thue-morse/sharp-check-results.json
```

The toolchain is pinned by the existing `lean-toolchain` to
`leanprover/lean4:v4.33.1`. The recorded `#print axioms` results contain only
`propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`, custom axiom,
or `native_decide` is used. The direct compiler invocation checks this
module. It is also integrated into the expanded default
build, whose current audit checks all selected endpoints and records
the exact source hashes in `verification/formal-audit.json`.

The Python file is a third, interval-based engine and diagnostic checker.
It compares exact lengths for starts 1 through 8191 with the existing
set-frontier output, compares complete small frontiers (including empty
ones) against direct edge expansion, and tests the dyadic table on a finite
range. These checks support implementation agreement and indexing only;
the universal theorem rests on the prose proof and Lean kernel check.
The separate sharp diagnostic also passes 18 full trajectory replays,
8,140 advance comparisons, and 256 bounded first-hit checks. The
[initial interval receipt](VERIFICATION.md) is historical; current
integrated verification is recorded in
[`FORMALIZATION-RECEIPT.md`](../../verification/FORMALIZATION-RECEIPT.md).

## Relationship to the existing proof and source

The [existing note](../../notes/THUE-MORSE-PATHS.md) obtains finiteness and a
quadratic numerical bound from offset monotonicity and overlap-freeness.
That quadratic bound can still be used as the interval engine's stopping
guard. The present interval theorem does not invoke overlap-freeness and
does not improve the numerical bound on its own. Its new contribution is
eliminating set-valued reachability from the infinite sharp-bound problem.

For the Thue-Morse structural source audit, Berstel and Seebold,
[*A characterization of overlap-free morphisms*, Discrete Applied Mathematics
46 (1993), 275-281](https://doi.org/10.1016/0166-218X(93)90107-Y), is the
primary research article already cited in the existing note. Its
[author-hosted PDF](https://igm.univ-mlv.fr/~berstel/Articles/1993OverlapFree.pdf)
and publisher metadata identify the overlap-free Thue-Morse morphism
setting. That imported theorem supports the prior quadratic argument; no
theorem from this paper is an assumption of the interval reduction or the
elementary binary-digit identities used above. No priority claim is made
for the reduction.
