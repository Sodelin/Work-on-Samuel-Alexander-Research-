# Finite-edit stability, exact three-child attainment, and a ten-proposal audit

**Status:** written mathematical audit and source packet, prepared 2026-09-24.
The new proofs in this document have not been checked by Lean in this audit.
The owning formalization task is responsible for translating them, checking
statement fidelity, and rebuilding the unified audit before changing their
verification status. No shared repository, proposal dossier, or Lean source
was edited to prepare this packet.

The two main findings are concrete. First, a finite change to a Thue–Morse
target preserves the sharp leading coefficient `8/3`, with an explicit
additive upper allowance. Second, the three-child productive core actually
has infinitely many vertices with exactly three children for every aperiodic
binary target. These statements concern the precise construction below.
They do not establish literature priority, a two-child impossibility theorem,
or empirical biological validity.

## 1. Exact construction and inspected source state

Let `s : N -> {0,1}` and write `not a = 1-a`. Define

```math
r_s(2j)=s(j),\qquad r_s(2j+1)=1-s(j).
```
The labelled edge predicate is

```math
E_s(u,w,a)\iff w\ge2\ \land\
\big[(w=u+1\land a=r_s(w))\ \lor\
(w=u+2\land a=1-r_s(w))\big].
```
In particular, the edge `0 -> 1` is absent. The roots are 0 and 1, and every
vertex `w >= 2` has one incoming edge of each binary label. These are the
equations in Section 2 of the classification manuscript [S1].

A **finite matching path of length ell** is a list of vertices
`p_0,...,p_ell` satisfying `E_s(p_k,p_(k+1),s(k))` for every `k < ell`.
There is no assumption that the path extends infinitely. Equivalently, use a
function `p : N -> N` with edge obligations only for `k < ell`; values beyond
`ell` are irrelevant. All new upper bounds below quantify directly over these
finite paths.

The following files were inspected in both checkouts where available:

- Audit checkout: `work/repo/lean/SamuelAlexanderResearch/` under the workspace
  containing this output.
- Active owner checkout: the sibling `alexander-formalization` checkout,
  with sources under `lean/SamuelAlexanderResearch/`.

| File | Observed SHA-256 | Observation |
|---|---|---|
| `BinaryAvoidance.lean` | `CEC0B9D6229A50EC7C4CAE25B121C31B6CAF1AF82AE595BCE0F9A28C01C84F8A` | Identical bytes in both checkouts. `row`, `Edge`, and `Matches` begin at lines 11, 14, and 18; `path_lower_bound` begins at line 34. |
| `SharpThueMorse.lean` | `A2F29F779A19191630D118C5D851FA475E3D0151D55793A0867FEAB50D4BA0EE` | Identical bytes in both checkouts. The finite-path bound is `binary_path_prefix_bound`; the attained family is `sharp_equality_family`. |
| `FixedGenderLift.lean` | `29FF78BD3B21A0340F5255C01B07604F3611C6FD3EA53A1878E33B4C3EA036D6` | Active owner source inspected. Contains `core_child_cap_three`, `core_inspecies`, and the induced-graph endpoints. This audit did not compile it. |
| `TEN-RESEARCH-IDEAS.md` | `AB16CCCDBA4E4D450778089647E8EDD0622021FB0BD70CD4941511607153A3A8` | Version reviewed in the active owner checkout. Later edits can supersede line numbers and proposal status. |

The inspected `BinaryAvoidance.path_lower_bound` assumes **infinite**
`Matches s path`. It cannot simply be invoked on a finite prefix that might
not extend. Lemma 2.1 below supplies the finite induction needed for the new
proofs. The existing sharp endpoint, by contrast, already quantifies over
finite prefixes of the actual edge predicate.

## 2. A general finite-prefix transport lemma

### 2.1 Finite offset and step bounds

For every finite matching `s`-path of length `ell` and every `0 <= k <= ell`,

```math
p_k\ge2k,\qquad p_0+k\le p_k\le p_0+2k.
```
**Proof.** Each edge increases its vertex number by one or two, which proves
the second pair of bounds by induction. For the first, the base case is
`p_0 >= 0`. Suppose `p_k >= 2k` and `k < ell`. If `p_k >= 2k+1`, either
allowed step gives `p_(k+1) >= 2k+2`. Otherwise `p_k=2k`. A step of one
would enter `2k+1` with label `r_s(2k+1)=1-s(k)`, contradicting the required
label `s(k)`; for `k=0`, that edge is also absent. Thus the step must be two.
This proves the induction without assuming any edges after depth `ell`.

### 2.2 Agreement of tails implies agreement of late graph edges

Suppose `s(k)=q(k)` for every `k >= m`. Then `r_s(w)=r_q(w)` for every
`w >= 2m`, since `floor(w/2) >= m`. Consequently, for every target vertex
`w >= 2m` and every `u,a`,

```math
E_s(u,w,a)\iff E_q(u,w,a).
```
The agreement condition concerns the **target vertex** of an edge. No claim
about the source vertex being large is required.

### 2.3 Backward realization of a finite prescribed prefix

For any binary target `q`, integer `m >= 0`, and vertex `w >= 2m`, there is a
length-`m` path `a_0,...,a_m=w` in `P_q` whose forward labels are
`q(0),...,q(m-1)`. Its start `u=a_0` satisfies

```math
w-2m\le u\le w-m.
```
**Proof.** When `m=0`, use the length-zero path at `w`. Otherwise choose
parents backward, requesting labels in the order `q(m-1),...,q(0)`.
Before the `(j+1)`st backward choice, with `0 <= j < m`, the current vertex
is at least `w-2j >= 2(m-j) >= 2`. It therefore has an incoming edge of the
requested label. Each backward step subtracts one or two, proving the stated
bounds. Ending at root 0 or root 1 is allowed; the construction never needs
to choose a parent of that endpoint.

### 2.4 Transport theorem for arbitrary binary targets and every finite length

Assume `s(k)=q(k)` for all `k >= m`. If a finite `s`-matching path of any
length `ell >= 0` starts at `v`, put `r=min(m,ell)`. Then a finite
`q`-matching path of the **same length** starts at some `u` with

```math
u+r\ge v,\qquad u\le v+r.
```
Thus, as integer inequalities, `|u-v| <= min(m,ell)`. This formulation
incorporates the stronger short-path observation supplied by the independent
side audit.

**Proof.** Write `w=p_r`. By Lemma 2.1, `w >= 2r`. Prepend the length-`r`
prefix from Lemma 2.3 for target `q`, ending at `w`. If `ell<m`, then
`r=ell` and there is no suffix: this prefix is already the entire required
path. If `ell>=m`, then `r=m`; keep the original suffix
`p_m,...,p_ell`. Every suffix edge has target vertex at least `2m`, so
Lemma 2.2 transfers it from `P_s` to `P_q`; its label at original index
`k>=m` also equals `q(k)`. Concatenation gives the desired path.

Both old and new starts lie in the integer interval `[w-2r,w-r]`, because
each of their first `r` steps has size one or two. Their distance is
therefore at most `r`, proving the displayed bounds. When `r=0`, including
`m=0` or `ell=0`, the construction has `u=v` and uses a length-zero prefix.

This theorem is symmetric in `s,q`. It does not assume aperiodicity,
computability, existence of maximum path lengths, or a Thue–Morse target.
It transports finite witnesses; it does not provide an infinite-path
compactness theorem by itself.

If finite maxima are separately known to exist at the relevant starts, an
immediate envelope corollary is

```math
L_s(v)\le\max\{L_q(u):u\in\mathbb N,\ |u-v|\le m\},
```
and the symmetric inequality with `s,q` interchanged. Include zero among
the possible nearby starts. The finite-path theorem is primary; this
corollary does not silently assume unproved existence of maxima.

## 3. Finite edits preserve the sharp Thue–Morse coefficient

Let `t(n)` be the parity of the number of ones in the binary expansion of
`n`. Fix `m >= 0` and a target `s` with `s(k)=t(k)` for every `k >= m`.
The argument uses the following existing sharp results as inputs:

1. Every finite `t`-matching path of length `ell` from `u >= 1` satisfies
   `3ell <= 8u-1`.
2. For each `n >= 0`, there exists a matching path from
   `v_n=3*2^n-1` of length `ell_n=8*2^n-3`.

The inspected Lean endpoints are `binary_path_prefix_bound` and
`sharp_equality_family`, together with `binary_edge_iff` and the definition
of finite reachability. The second input requires only the attained finite
path, not maximality of that path.

### 3.1 The zero-start exception for the original target

The standard identities `t(2j)=t(j)` and `t(2j+1)=1-t(j)` give
`r_t(w)=t(w)` for every `w`. This is the substitution of actual Thue–Morse
bits for row labels used below; it is also the inspected
`SharpThueMorse.binary_row_eq` endpoint.

Every `t`-matching path from 0 has length at most one, and the one-edge path
`0 -> 2` exists. Indeed `t(0)=0`, `t(1)=1`, `t(2)=1`, `t(3)=0`, and
`t(4)=1`. The only edge out of 0 goes to 2 and has label `1-t(2)=0`, so it
matches the first bit. At the next step, both possible labels out of 2 are
0: the edge to 3 has label `t(3)=0`, and the edge to 4 has label
`1-t(4)=0`. Neither matches `t(1)=1`.

This finite check is given as a written argument here. It must be added as
a lemma or discharged directly if the formal implementation needs it.

### 3.2 Explicit upper bound, formulated only for finite paths

**Theorem.** For every `v >= 1`, every `ell >= 0`, and every finite
`s`-matching path of length `ell` from `v`,

```math
\boxed{3\ell\le8v+8m-1.}
```
**Proof, including all boundary cases.**

- If `m=0`, then `s=t` everywhere and the existing sharp finite-path bound
  proves the result directly.
- Suppose `m>=1` and `ell<m`. Then `ell<=m-1`, so
  `3ell<=3m-3<=8v+8m-1`.
- Suppose `m>=1` and `ell>=m`. The transport theorem gives a matching
  `t`-path of length `ell` from some `u<=v+m`. If `u>=1`, the sharp bound
  gives `3ell<=8u-1<=8v+8m-1`.
- In the remaining case `u=0`, Section 3.1 gives `ell<=1`, hence
  `3ell<=3<=8v+8m-1` because `v>=1`. No positive-start theorem is applied
  at zero.

The hypotheses contain no claim that `L_s(v)` already exists. As a later
elementary corollary, the set of attainable lengths from any `v>=1` is
nonempty (it contains zero) and bounded by this theorem, so it has a largest
element. Only after this observation is the notation `L_s(v)` needed.

### 3.3 Sharpness survives, via nearby starting vertices

For every sufficiently large `n` with `ell_n >= m` and `v_n > m`, transport
the existing sharp `t`-path to an `s`-path. This gives an actual finite path
of length `ell_n` from a positive vertex `u_n` satisfying

```math
|u_n-v_n|\le m,\qquad
\ell_n=\frac{8v_n-1}{3}.
```
In particular `u_n -> infinity`. These nearby starts are the reason finite
edits cannot destroy asymptotic sharpness, even if they destroy matching
paths from the original extremal indices themselves.

**Coefficient-optimality theorem without maximum notation.** For every
real `c < 8/3` and every real additive constant `B`, there are `v>=1`,
`ell>=0`, and an actual finite `s`-matching path from `v` of length `ell`
such that `ell > c*v+B`.

**Proof.** Use the witnesses `u_n,ell_n` above. Since `|u_n-v_n|<=m`,

```math
\ell_n-cu_n
\ge(8/3-c)v_n-1/3-|c|m\longrightarrow+\infty.
```
The absolute value handles negative `c` as well as nonnegative `c`.
Eventually the expression exceeds `B`.

Once maxima have been defined using the boundedness corollary, the upper
bound and the attained paths give the equivalent statement

```math
\boxed{\limsup_{v\to\infty}\frac{L_s(v)}v=\frac83.}
```
This does not assert that all starts attain the ratio, that the original
exact equality indices survive, or that the explicit allowance `8m-1` is
the best possible additive allowance for a particular edit.

### 3.4 Relation to prior work and proposal wording

Alexander already backward-extends a finite prescribed prefix in the proof
of Theorem 6 of arXiv:1212.0186v2 [S8]; the classification manuscript cites
the published theorem as Theorem 10 and uses the method in Section 4 [S1].
The result here is a quantitative transport
statement for its particular bounded-step graph and a corollary of the
existing sharp theorem. Accordingly, replace the proposal's claim that
lower sharpness may fail because the attainable states miss the extremal
family. Nearby starts supply the required witnesses. A defensible research
extension is to determine optimal edit-dependent additive constants or
exact transported equality families.

The bounded source review did not identify a publication stating this
specific sharp coefficient corollary. It does not establish first discovery
or literature priority.

## 4. The productive core has exactly three children infinitely often

### 4.1 Lift and retained vertices

Use vertices `(v,a)` with `v in N`, `a in {0,1}`, and permanent gender `a`.
Put an edge from `(v,a)` to `(w,b)` exactly when `E_s(v,w,a)`; the target
gender `b` is unrestricted. Every lifted edge therefore has its source's
permanent gender. Define the active set

```math
A_s=\{(v,a):\exists w\ E_s(v,w,a)\}.
```
The core is the graph induced on `A_s`; deleted copies are not vertices and
must not be counted as new roots. The active owner source encodes
`(v,a)` as `2v+bit(a)`.

The finite-alphabet lift is in Section 3 of the classification manuscript
[S1]. The active-set restriction and its three-child property are an
additional analysis of that lift.

### 4.2 Exact active genders

The following identities follow directly from the edge equations:

```math
\begin{aligned}
\{a:(0,a)\in A_s\}&=\{1-s(1)\},\\
\{a:(2j+1,a)\in A_s\}&=\{s(j+1)\}\qquad(j\ge0),\\
\{a:(2k,a)\in A_s\}&=\{1-s(k),1-s(k+1)\}\qquad(k\ge1).
\end{aligned}
```
**Proof.** Base vertex 0 has only child 2, with label `1-r_s(2)=1-s(1)`.
For the odd base `2j+1`, the outgoing edge to `2j+2` has label `s(j+1)`;
the outgoing edge to `2j+3` has label `1-r_s(2j+3)=s(j+1)` as well.
For the positive even base `2k`, the outgoing labels are
`r_s(2k+1)=1-s(k)` and `1-r_s(2k+2)=1-s(k+1)`. These are all possible
child indices. The exception at base 0 must be retained because `0 -> 1`
is absent.

Thus every odd base has exactly one active copy. A positive even base has
two active copies precisely at an adjacent change `s(k) != s(k+1)`;
otherwise it has one.

### 4.3 Upper cap three

Every lifted source can have children only over its next one or two base
indices, namely `v+1` and `v+2`, subject to the source label. Among those
indices one is odd and supports exactly one active copy; the even index
supports at most two. Consequently every retained source has at most three
distinct retained children.

This upper-cap statement appears as `core_child_cap_three` in the inspected
active source. The new claim below is its attainment, not a substitute for
the population and induced-graph checks.

### 4.4 Exact attainment formula

For each `j>=0`, let

```math
x_j=(2j+1,s(j+1)).
```
It is the unique active copy over `2j+1`. Both outgoing base edges have its
gender, so its children in the induced core are **exactly**

```math
\{(2j+2,b):b\in\{1-s(j+1),1-s(j+2)\}\}
\ \cup\ \{(2j+3,s(j+2))\}.
```
The sets lie over different base indices. The even-base part has two
distinct vertices precisely when `s(j+1) != s(j+2)`. Therefore

```math
\deg^+_{A_s}(x_j)=
\begin{cases}
3,&s(j+1)\ne s(j+2),\\
2,&s(j+1)=s(j+2).
\end{cases}
```
This counts **distinct child vertices**, as the population cap requires;
it is not a count of labels or paths.

### 4.5 Infinitely many three-child vertices

If `s` is not eventually constant, there are infinitely many indices
`k>=1` with `s(k) != s(k+1)`. Otherwise the finitely many changes have a
largest index, after which induction makes every successive bit equal,
contradicting non-eventual constancy. Each such `k=j+1` gives the distinct
vertex `x_j` of outdegree three by Section 4.4. Thus the induced core has
infinitely many three-child vertices.

In particular this applies when `s` is not eventually periodic, because an
eventually constant sequence has eventual period one. The hypothesis needed
for attainment is weaker than the hypothesis needed for self-avoidance.

### 4.6 Why further ancestral pruning cannot solve cap two

For this lift, any active copy reaches both copies over some child base
`w>=2`. Once both copies over a base `z>=1` have been reached, the copy
whose gender is `r_s(z+1)` has edges to both copies over `z+1`. Induction
therefore reaches every copy over every sufficiently late base. Every
intermediate vertex on a path ending at an active vertex is itself active,
because it has a next edge. These paths consequently survive in the induced
core when their endpoint is retained.

There is at least one active copy over every base index, so the core is
infinite. The preceding paragraph shows that every core vertex has
cofinitely many core descendants. It follows directly that every infinite
ancestor-closed subset `T` of the core is the whole core: for any core vertex
`x`, an infinite `T` intersects the cofinite descendant set of `x`; ancestral
closure then forces `x` into `T`.

This is the inspecies minimality mechanism in Alexander's Definition 4 and
Propositions 5–6 [S2]. The active owner source contains `core_inspecies` and
`core_induced_inspecies`, implementing the corresponding statements.

Consequently a smaller **infinite ancestor-closed induced vertex subset**
of this core cannot eliminate its three-child vertices. This does not rule
out edge deletion with repairs, a subset that is not ancestor closed, a
different lift, or a completely different two-child construction. It does
not prove `d_vertex(s)=3`.

### 4.7 Earlier inspecies avoiders and the remaining distinction

The companion `OLDER-CONSTRUCTIONS-AND-RANK-AUDIT.md` derives cofinite
descendants, hence whole-graph inspecies, for Alexander's older `T_h` and
`H_h` constructions [S8]. Thus merely giving some fixed-gender inspecies
avoider is already implicit in that work. Their displayed avoidance proofs
use `h(n) -> infinity`; the companion's degree calculation gives maximum
outdegree `h(n)+1` in generation `n`. The relevant comparison here is the
uniform cap three for an arbitrary prescribed aperiodic binary target.
This comparison does not exclude bounded-`h` variants; it supplies no
priority certificate for the stronger combination.

## 5. Full audit of the ten research proposals

The dossier correctly calls its entries proposals and makes no claim to know
Alexander's private work. Verification status must still be synchronized
with the owner's final receipts. The following assessments are written
mathematical/source review, not additional kernel certificates.

### Proposal 1: the two-versus-three fixed-gender threshold

The active-copy cap-three seed is well motivated and matches the inspected
edge equations. Add the exact-attainment theorem in Section 4 and the
limitation on ancestor-closed pruning. The first decisive cap-two test should
preserve source gender, incoming coverage, simplicity, and all population
axioms; finite failed searches do not prove nonexistence. An infinite witness
must have a construction rule and an avoidance proof. The inspected source
gives a cap-four lift; no inspected source in this bounded review gives the
cap-three pruning result [S1]. The older inspecies avoiders in Section 4.7
must also be credited: whole-inspecies avoidance alone is not the proposed
distinguishing feature.

### Proposal 2: minimal crossing count and eventual ray powers

The proposed equality analysis appears sound. State simplicity, a complete
birth-order enumeration, and eventual indegree and outdegree exactly `k`.
At a sufficiently late cut, the next `k` vertices require at least
`k,k-1,...,1` incoming edges crossing the cut. If the total is
`k(k+1)/2`, every lower bound is tight: all available internal edges among
those `k` vertices occur, and no crossing edge terminates after the block.
Apply the last assertion to every sufficiently late cut to bound all tail
edge lengths by `k`. Full outdegree then forces exactly the edges
`v -> v+1,...,v+k`. This is a direct proof route before any broad search.

For `k=2`, permanent genders on this eventual `+1,+2` graph must alternate:
the two parents of each nonroot have different genders. From a sufficiently
late vertex of the requested initial gender, choose a `+1` or `+2` step to
make the next source gender opposite or equal, as required. Thus it realizes
every binary word. This supplies the claimed obstruction at minimal width,
conditional on the equality theorem. No exact prior match was verified in
the bounded cutwidth search; a priority claim would need a wider graph-layout
literature review.

### Proposal 3: finite-port descriptions

The representation target is useful, but the standard automata conclusion
should be explicit: an omega-regular language containing every ultimately
periodic word is the full omega-language. Otherwise its omega-regular
complement has an ultimately periodic witness [S3].

The new obligation is proving that an eventually periodic complete port
encoding yields the **exact** realization language as an omega-regular
language. Track source equivalence needed for simplicity and require every
pending edge to terminate at a finite birth. A permanently occupied port
does not define an edge to a vertex at infinity. Merely having finitely many
ports does not make an arbitrary time-dependent schedule finite-state. The
first test remains reversible encoding/decoding with path preservation at
widths three and four.

### Proposal 4: a finite binary-digit description of all maxima

The `2`-regularity question is precise. Define `L(0)` before taking the
`2`-kernel; Section 3.1 gives `L_t(0)=1`. Allouche–Shallit is the direct
framework [S4]. Add `2`-synchronization as a stronger candidate: a finite
automaton recognizing binary pairs `(v,L(v))` would imply `2`-regularity,
using the established synchronized-sequence theory [S5]. Neither conclusion
follows from automaticity of `t` or of a one-step transition.

Require a computational search to output candidate coupled functions and
identities for their even/odd arguments. Prove their closure and initial
conditions. A stable-looking rank of finite tables is only a conjecture
generator. Ordinary factor matching, separators, and longest common
subsequences are neighboring objects, not automatically this path function.

### Proposal 5: phase shifts

The model distinction is correct: for `s_a(k)=t(k+a)`, the corresponding row
is `r_(s_a)(w)=t(w+2a)`. Keeping `P_t` fixed instead gives consecutive-edge
realizations of the shifted target from `a-1` for `a>=2`. That is a different
question. Normalize the changed graph by the coordinate `w+2a` and track
the relative target phase before starting an expensive search. The phase-zero
sharp proof does not establish the coefficient for all phases.

### Proposal 6: quantitative aperiodicity

Replace the vague modulus with, for example,

```math
M_s(K,p,\epsilon)=\min\{j\ge K:
s(j+p)\ne s(j)\mathbin{\mathrm{xor}}\epsilon\},
\qquad p>0,\ \epsilon\in\{0,1\}.
```
Non-eventual periodicity makes it finite for both values of `epsilon`:
eventual equality gives period `p`, while eventual antiperiodicity gives
period `2p`. Stable offset plateaus can then be bounded by these failure
times. The modulus must account for the evolving starting index, not merely
the first failed comparison of an initial prefix.

The arbitrary-computable-growth target has an elementary candidate route:
at stage `n`, repeat the current prefix of length `p_n` long enough to beat
`f(2p_n-1)` using the checked periodic-prefix seed; afterwards extend the
word to defeat the next enumerated eventual-period pair `(K,q)`. Ensure
prefix lengths strictly increase and the diagonal witness indices are fresh.
This is a proof plan, not a completed construction in this packet. The source
already observes the absence of a uniform target-independent bound [S1].

### Proposal 7: finite edits

Sections 2–3 supply a written proof of the main proposed coefficient theorem,
including all short-path and zero-start cases. Update the entry to a proof
candidate awaiting Lean, then direct further exploration toward sharp
additive allowances and exact extremal starts under edits. Credit the
backward-prefix method [S1].

### Proposal 8: a general productive-core theorem

Use infinitely many strict descendants as generic productivity. Having one
child is sufficient only in the special lift after the cofinite-future
argument is established. For an infinite eligible population with whole-graph
IAP, the proposed core should be an eligible inspecies: finite roots and
finite branching yield an infinite productive core; every parent of a
productive vertex is productive; IAP makes every productive future cofinite.

There is also a uniqueness deduction: every inspecies vertex has infinitely
many descendants by Alexander's Proposition 6 [S2], so every inspecies is
contained in the productive core. Once that core is itself an inspecies,
minimality leaves only this one. The more substantive open extension is
whether ambient pruning commutes with taking a particular maximal cluster;
that requires separate hypotheses or a counterexample.

### Proposal 9: incoming-label repair at a boundary

The repair mechanism is already explicit in the source [S1]. For a **fixed**
retained cofinite vertex set and edge-deletion-only repairs, each retained
nonroot missing an incoming label must lose all its remaining incoming edges:
deletion cannot restore the missing label. No other edges need deletion.
Thus the least edge-deletion repair is already forced in this model.
Allowing vertex deletion, added edges, or costs for new roots creates different
optimization questions and must be specified.

Whole-graph IAP also appears stable under finite deletions under the stated
finite-branching and finite-birth-sublevel hypotheses. If a surviving vertex
still has infinitely many descendants, finite branching provides a
sufficiently late descendant that itself has infinitely many surviving
descendants. Choose it after all altered endpoints. Its future edges are
unchanged, and original IAP makes that future cofinite. An arbitrary late
descendant is insufficient here because it might be terminal. Connectedness
can fail. This is a written proof sketch requiring its own formal statement;
it is not claimed to preserve every cluster predicate.

### Proposal 10: stateful cellular-automaton potentials

The inequality `u dot d <= c+h(q)-h(q')` is a standard finite weighted-graph
potential certificate. Its optimum is controlled by the maximum cycle mean,
equivalently a sign-reversed instance of classical cycle-mean optimization
[S6]. The substantial work is a sound local-rule state graph and a strictly
improved certificate for a specific rule.

State the quantified object: every causal path, an Alexander-selected
lifeline, spaceship translation, or the whole activity front. Existence of
one slow lifeline does not alone bound the speed of every live cell. For a
bounded-width translating spaceship, a suitable lifeline shares its average
translation velocity, but that argument needs to be included.

Johnston already proves the `c/3` diagonal and `c/2` orthogonal spaceship
bounds for the 2x2 rule, with an oblique-direction consequence [S7]. Reproving
them with potentials is a certificate or formalization contribution. A speed
improvement needs a valid comparison with the applicable published bound for
the same rule and class of configurations.

## 6. Primary sources and scope of the search

- **[S1]** *A classification of biologically unavoidable sequences*, manuscript
  dated 10 September 2026. [Pinned source manuscript](https://raw.githubusercontent.com/avg-netizen/biological-unavoidability/3d6175e3e23f67bd68e7be591b5a9a6d04e496a3/paper.md).
  Sections 2–4 were checked for the exact row/edge equations, the displayed
  vertex-gender lift, and the backward-prefix/boundary-repair method. The
  coordinating source auditor verified the pinned commit
  `3d6175e3e23f67bd68e7be591b5a9a6d04e496a3` and its manuscript.
- **[S2]** Samuel A. Alexander, *Infinite graphs in systematic biology, with
  an application to the species problem*. [Author's arXiv paper](https://arxiv.org/html/1201.2869).
  Definition 4 and Propositions 5–6 supply the inspecies comparison.
- **[S3]** *Saturation Problems for Families of Automata*, ICALP 2025.
  [Primary conference paper](https://drops.dagstuhl.de/storage/00lipics/lipics-vol334-icalp2025/html/LIPIcs.ICALP.2025.146/LIPIcs.ICALP.2025.146.html).
  Its introduction explicitly recalls determination of omega-regular
  languages by their ultimately periodic words and attributes the classical
  result to Büchi's theory.
- **[S4]** Jean-Paul Allouche and Jeffrey Shallit, *The ring of k-regular
  sequences*, Theoretical Computer Science 98 (1992), 163–197.
  [Publisher DOI](https://doi.org/10.1016/0304-3975(92)90001-V).
- **[S5]** Arturo Carpi and Cristiano Maggi, *On synchronized sequences and
  their separators*, RAIRO–Theoretical Informatics and Applications 35(6)
  (2001), 513–524. [Primary paper PDF](https://www.numdam.org/item/ITA_2001__35_6_513_0.pdf),
  [DOI](https://doi.org/10.1051/ita:2001129). This is the source for the
  synchronized/regular framework, not a result about the current path lengths.
- **[S6]** Richard M. Karp, *A Characterization of the Minimum Cycle Mean in
  a Digraph*. [Berkeley technical-report record](https://www2.eecs.berkeley.edu/Pubs/TechRpts/1977/29121.html),
  [published DOI](https://doi.org/10.1016/0012-365X(78)90011-0).
- **[S7]** Nathaniel Johnston, *The B36/S125 “2x2” Life-Like Cellular
  Automaton*, Theorem 3.1 and its following discussion.
  [Author's arXiv paper](https://arxiv.org/html/1203.1644).
- **[S8]** Samuel A. Alexander, *Biologically unavoidable sequences*.
  [arXiv:1212.0186v2](https://arxiv.org/html/1212.0186v2), Theorem 6 and
  Definitions 6 and 8. The theorem numbers here refer to that specific
  preprint version.

The focused search used twelve queries in three batches: the regular-sequence,
cycle-mean, omega-automata, and Alexander-inspecies sources; exact biological
unavoidability/three-gender terms, finite modification/Thue–Morse terms,
cellular-automaton potential terms, and acyclic regular cutwidth terms; then
cellular-automaton cycle means, de Bruijn speed limits, Carpi–Maggi
synchronization, and Thue–Morse coalescence terms. Primary pages were opened
for the claims used here. Search-engine dates were not used to establish
publication priority.

No exact prior publication for the two main new written claims was verified
in this bounded pass. Both are elementary deductions from the specified
construction plus existing inputs. Their interest, their correctness, their
formal verification, and their publication priority are four separate
assessments. The packet supports the first two through explicit statements
and proofs; the owner must complete Lean verification and any broader
priority review.

## 7. Suggested formalization boundary

The finite-edit work can be kept small and compositional:

1. Define finite prefix matching for an arbitrary target using the existing
   `BinaryAvoidance.Edge`.
2. Prove the finite offset induction and the one/two-step distance bounds.
3. Prove row/edge agreement above twice the target cutoff.
4. Build a finite labelled prefix backward from a sufficiently high vertex.
5. Prove symmetric finite-prefix transport with `r=min(m,ell)`, `u+r>=v`,
   and `u<=v+r`, including the empty-suffix case `ell<m`.
6. Prove the zero-start Thue–Morse length bound and transfer the checked sharp
   upper bound to all edited finite paths.
7. Transport the checked attained family. State coefficient optimality using
   finite witnesses, before defining maxima or adding real asymptotic notation.

The cap-three attainment work can use `odd_core_gender` and add the
positive-even active-gender equivalence, the exact three-element child set at
an adjacent change, and the elementary unbounded-change-index lemma. Keep
this independent from the unresolved cap-two existence question.

**Not Lean checked by this packet:** the new finite-prefix transport,
finite-edit upper theorem, transferred coefficient sharpness, exact child-cap
attainment, infinite attainment, and additional proposal-level deductions.
Existing source files and named endpoints were inspected, not recompiled.
Any later checked implementation should record its own source hashes,
endpoint axioms, theorem-to-prose review, and integrated build receipt.
