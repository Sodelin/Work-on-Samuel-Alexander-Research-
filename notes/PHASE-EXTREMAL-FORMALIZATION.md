# Exact equality for phase-shifted Thue–Morse paths

`lean/SamuelAlexanderResearch/PhaseExtremal.lean` proves the exact equality classification in the actual graph built from the shifted Thue–Morse target. Let $`t`$ be the checked binary digit-parity sequence, put $`s_{a}(k)=t(k+a)`$, and let $`L_{a}(v)`$ denote the maximum number of edges in a phase-zero $`s_{a}`$-matching path from $`v`$ in `BinaryAvoidance.Edge s_a`. For every $`a\ge 0`$ and $`v\ge 1`$, the maximum exists and

```math
3L_a(v)\le 8v+5a-1.
```
The new equality theorem is

```math
\boxed{\quad
3L_a(v)=8v+5a-1
\quad\Longleftrightarrow\quad
\exists n\ge0:\ a\le 2^n\ \text{ and }\ v=3\cdot2^n-a-1.
\quad}
```
At those starts, the exact maximum is

```math
L_a(3\cdot2^n-a-1)=8\cdot2^n-a-3\qquad(a\le2^n).
```
The finite-path model, original sharp bound, and phase transport come from the existing checked modules. The underlying binary population is attributed to the [September 2026 classification manuscript, Section 2](https://raw.githubusercontent.com/avg-netizen/biological-unavoidability/3d6175e3e23f67bd68e7be591b5a9a6d04e496a3/paper.md). The extremal step pattern was supplied as a candidate in the parallel source-side work and independently verified here. The pattern, its edge-label comparisons, and the converse equality argument are proved in Lean; no source-side proof is assumed as a premise, and no literature-priority claim is made.

## Exact formal endpoint and model

All matching statements use `BinaryAvoidance.Edge`, including its missing edge $`0\to 1`$. A phase shift changes both the target word and the graph constructed from it. These results do not concern reading a shifted target in the unchanged graph $`P_{t}`$.

`FiniteEditStability.IsMaximumPrefix s v len` means that an actual path function attains $`\ell`$ matching edges from $`v`$ and that every other attained matching length from $`v`$ is at most $`\ell`$. It is not an assumed numerical bound or an interval-model substitute for actual paths.

`PhaseExtremal.shifted_maximum_exists` proves that every positive start has such a maximum and that it satisfies the displayed upper bound. The main endpoint `PhaseExtremal.shifted_extremal_iff` states, for `a v len : Nat` with $`1\le v`$,

```lean
(FiniteEditStability.IsMaximumPrefix (PhaseShift.shift t a) v len ∧
  3*len = 8*v+5*a-1) ↔
  ∃ n, a ≤ 2^n ∧ v = 3*2^n-a-1 ∧ len = 8*2^n-a-3
```

The theorem therefore includes both attainment of the claimed equality family and exclusion of every other positive-start equality case. The positive-start restriction is essential to the stated classification. The zero-start problem is not included.

## The explicit extremal step construction

Write $`q=2^n`$. A step word records vertex increments $`1`$ and $`2`$, not Boolean target symbols. The constructed path starts at $`3q-1`$, has $`8q-3`$ edges, and ends at $`16q-6`$.

For $`q=1`$, the step word is

```math
D_1=11222,
```
with vertices $`2,3,4,6,8,10`$.

For dyadic $`q\ge 2`$, the recursive construction is

```math
D_q=
1^q\,2^{q-1}\,1\,2^{q+2}\;
\left(\prod_{r=1,2,4,\ldots,q/4}1^r2^r\right)\;
D_{q/2}.
```
The staircase product is empty when $`q=2`$. The **four initial runs have length $`3q+2`$**. The staircase adds $`q-2`$ edges, giving a complete head of length $`4q`$. The recursive tail has length $`4q-3`$; total length is $`8q-3`$.

The implementation builds actual finite paths using `Part`, `Segment`, and `joinPath`. `Part phase path len` checks each actual edge against $`t(\operatorname{phase}+i)`$. One-step and two-step segments use the explicit functions $`x+i`$ and $`x+2\cdot i`$. Concatenation preserves their shared endpoint and all early vertices. Thus the proof constructs the run pattern directly; it does not postulate a path with those comparisons.

### The four initial runs

| Run | Start time | Start vertex | Length | Final vertex |
| --- | ---: | ---: | ---: | ---: |
| Ones | $`0`$ | $`3q-1`$ | $`q`$ | $`4q-1`$ |
| Twos | $`q`$ | $`4q-1`$ | $`q-1`$ | $`6q-3`$ |
| One | $`2q-1`$ | $`6q-3`$ | $`1`$ | $`6q-2`$ |
| Twos | $`2q`$ | $`6q-2`$ | $`q+2`$ | $`8q+2`$ |

The first run uses $`t(3q+i)=t(i)`$ for $`i<q`$. The second uses $`t(2q+i)=t(q+i)`$ for $`i<q-1`$, after simplifying the label of its odd-destination two-step edge. The single step uses

```math
t(6q-2)=t(3q-1)=t(2q-1).
```
The last run uses $`\neg t(3q+i)=t(2q+i)`$ for $`i<q+2`$. Since $`q\ge 2`$, this range lies below $`2q`$, where the relevant high-bit comparisons are $`(3,2)`$ and $`(4,3)`$. Every equality follows from the existing proved binary-block identity for the actual sequence $`t`$.

### The staircase

At scale $`r`$, the staircase state is

```math
\text{time}=3q+2r,\qquad\text{vertex}=8q+3r-1.
```
The next $`r`$ ones and $`r`$ twos move it to the corresponding state with scale $`2r`$. Here $`q/r=M`$ is dyadic and at least four. The one-step comparisons have high blocks $`8M+3`$ and $`3M+2`$, both with Thue–Morse value true. After simplifying the odd-destination labels, the two-step comparisons have high blocks $`4M+2`$ and $`3M+3`$, both with value false.

`staircase_step` proves that transition, and `staircase` concatenates every required scale. `head_path` concludes that the complete head ends at

```math
\text{time}=4q,\qquad\text{vertex}=8q+3(q/2)-1.
```
It also records the first $`q`$ one-steps pointwise and proves that the next step is two.

### The translated half-size tail

Translate the $`D_{q/2}`$ path by $`8q`$ in vertex coordinates and by $`4q`$ in time. Its vertices are all below $`8q`$: its terminal vertex is $`8q-6`$, and every edge is increasing. Its edge times are below $`4q`$. Both shifts are powers of two, so they complement respectively the destination-row bit and the target bit. Complementing both preserves the label comparison for either edge length. `half_translate` proves this for actual edges, with the finite bounds established from the half-path's endpoint.

The tail begins exactly where the head ends and finishes at $`16q-6`$. Induction gives `extremal_path`. This endpoint records the exact start, length, terminal vertex, first $`q`$ one-steps, and, for $`q\ge 2`$, the next two-step. It asserts a finite prefix of an actual path function; values of that function after the prefix are immaterial.

## Attaining shifted equality

For $`a\le q`$, take the constructed original extremal path and remove its first $`a`$ edges. Those edges all have length one, so its vertex at time $`a`$ is $`3q-1+a`$. The already checked phase transport subtracts $`2a`$ from every remaining vertex. The resulting shifted path starts exactly at

```math
(3q-1+a)-2a=3q-a-1
```
and has $`8q-a-3`$ edges. It attains equality in the shifted upper bound. `shifted_family_prefix` supplies the actual path witness, and `shifted_equality_family` proves that this attained length is the maximum.

## Excluding every other equality case

Suppose a shifted matching path of length $`\ell`$ starts at $`v\ge 1`$ and satisfies $`3\ell=8v+5a-1`$. `PhaseShift.prepend_shifted_prefix` produces an original matching path of length $`\ell+a`$, starting at some $`u`$ with $`v\le u\le v+a`$. The original sharp inequality then forces

```math
u=v+a,\qquad 3(\ell+a)=8u-1.
```
`original_equality_dyadic` applies the original sharp equality classification to this actual finite path. Its maximality is derived from the saturated sharp bound, not assumed separately. Hence $`u=3q-1`$ and $`\ell+a=8q-3`$ for some dyadic $`q`$.

The prepended part ends at $`v+2a=u+a`$. Every edge advances by at least one, so a prefix of $`a`$ edges whose total advance is exactly $`a`$ consists entirely of one-steps. `initial_ones_of_minimum_displacement` proves that statement pointwise from finite edge geometry.

To compare this path with the constructed extremal path, `extremal_terminal` uses the checked interval frontier and its actual-edge bridge to prove that **every** length-$`8q-3`$ path from $`3q-1`$ ends at the single vertex $`16q-6`$. In the actual binary graph, a destination and label determine the incoming parent uniquely; `incoming_unique` proves this directly from the two possible incoming edges. Backward induction in `prefix_unique_of_endpoint` therefore fixes the entire finite path. `extremal_prefix_unique` combines these facts.

For $`q\ge 2`$, the unique extremal path's step at time $`q`$ has length two. The prepended one-step prefix consequently cannot extend past time $`q`$, proving $`a\le q`$. For $`q=1`$, its first two steps are both one, but $`u=2=v+a`$ and $`v\ge 1`$ already force $`a\le 1=q`$. This handles the base case without an incorrect uniform claim about the first non-one step.

`shifted_equality_necessary` proves this necessity even for a finite matching witness that is not initially supplied with a maximum certificate. Combining it with the attained family gives `shifted_extremal_iff`.

## Verification and scope

From the repository root in PowerShell:

```powershell
$env:ELAN_HOME = 'C:\Users\Owner\.elan'
$env:PATH = 'C:\Users\Owner\.elan\bin;' + $env:PATH
& 'C:\Users\Owner\.elan\bin\lake.exe' env lean lean/SamuelAlexanderResearch/PhaseExtremal.lean
```

The module passes Lean 4.33.1 with the existing Std-only dependency tree and emits no warnings. Its nine selected axiom checks pass, using only subsets of `propext`, `Classical.choice`, and `Quot.sound`. There are no `sorry`, custom axioms, `native_decide` endpoints, or Mathlib additions. All run comparisons and the full equality classification are universal proofs; no larger finite scan was used.

The module changes no earlier theorem or file. It strengthens the earlier phase-shift existence interval to an exact attained family and gives the complete equality classification for positive starts. It does not provide a standalone executable step-word generator, a classification at start zero, a formula for every nonextremal shifted maximum, or a theorem about a shifted target in the unchanged original graph. Literal real-number coefficients and limit statements remain in the separate real adapter.
