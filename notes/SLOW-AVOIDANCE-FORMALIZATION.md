# Arbitrarily long finite matches without an infinite match

`lean/SamuelAlexanderResearch/SlowAvoidance.lean` proves the proposed slow-avoidance result for the actual `BinaryAvoidance.Edge` construction. For **every** function `f : Nat → Nat`, it constructs a Boolean word $`s`$ that is not eventually periodic and has no infinite matching path, together with strictly increasing starting vertices $`v_{j}`$ and finite matching paths of lengths greater than $`f(v_{j})`$.

The theorem does not assume that $`f`$ is increasing or computable. Its word is defined by executable Lean recursion relative to the supplied function $`f`$. This is not a formal theorem about Turing computability or running-time complexity. The underlying binary avoiding graph and the theorem that it avoids its aperiodic target are attributed to the [classification manuscript, Section 2](https://github.com/avg-netizen/biological-unavoidability/blob/main/paper.md). The repeated-prefix and zero-block diagonal construction below is the proposed extension verified in this module; no claim of literature priority is made.

## Exact statement

The exported endpoint `SlowAvoidance.arbitrarily_slow_avoidance` has no hypothesis on $`f`$:

```lean
(f : Nat → Nat) :
  ∃ s : Nat → Bool, ¬ EventuallyPeriodic s ∧
    (¬ ∃ path, Matches s path) ∧
    ∃ starts : Nat → Nat,
      (∀ i j, i < j → starts i < starts j) ∧
      ∀ j, ∃ len, f (starts j) < len ∧
        ∃ path : Nat → Nat,
          path 0 = starts j ∧ MatchesPrefix s path len
```

`MatchesPrefix s path len` checks the actual edge relation for every index $`k < \ell`$, reading target bit $`s(k)`$ on the kth edge. Thus $`\ell`$ counts edges, and each finite match starts at phase zero. The absence of an infinite match is separately proved for this same constructed word and this same graph. No finite experiment is used to establish either assertion.

## The construction

Conceptually, define finite words by

```math
W_0=[\mathrm{true}],\qquad p_j=|W_j|,\qquad v_j=2p_j-1,
```
```math
r_j=f(v_j)+2,\qquad M_j=r_jp_j,
```
```math
W_{j+1}=W_j^{r_j}\;\Vert\;
          [\mathrm{false}]^{M_j}\;\Vert\;[\mathrm{true}].
```
The Lean implementation represents a finite word by its length and a total bit function, using only positions below that length. This avoids an incidental list-indexing layer while preserving the stated finite concatenation exactly:

- `wordLength f 0 = 1` and `wordBit f 0 k = decide (k = 0)`.
- `blockLength f j = (f (start f j) + 2) * wordLength f j`.
- `wordLength f (j+1) = 2 * blockLength f j + 1`.
- At stage $`j+1`$, positions $`k < M_{j}`$ read the old word at $`k \bmod p_{j}`$; positions $`M_{j} \le k < 2M_{j}`$ are false; position $`2M_{j}`$ is true. Later positions are outside the finite word and are immaterial.

Since $`r_{j} \ge 2`$, $`W_{j}`$ is a prefix of $`W_{j+1}`$. The lengths strictly increase and satisfy $`p_{j} \ge j+1`$. The limit is therefore defined without an existential choice of an infinite extension:

```math
s(k)=\operatorname{wordBit}(f,k+1,k).
```
`wordBit_extends`, `wordBit_coherent`, and `target_agrees` prove that any bit already inside any stage is exactly the corresponding limit bit. The definition samples stage $`k+1`$, whose proved length bound is sufficient to contain index $`k`$.

## Long finite paths

Define the comparison length

```math
\ell_j=(f(v_j)+1)p_j=(r_j-1)p_j.
```
Both positions $`k`$ and $`k+p_{j}`$ lie in the repeated block whenever $`k < \ell_{j}`$. Their remainders modulo $`p_{j}`$ are equal. Prefix coherence therefore gives

```math
s(k+p_j)=s(k)\qquad(k<\ell_j).
```
`target_periodic_prefix` proves this identity. `QuantitativeAvoidance.periodic_prefix_gives_match` then supplies a matching path with $`\ell_{j}`$ edges starting at $`v_{j}=2p_{j}-1`$. Its explicit form is $`\operatorname{path}(k)=2k+v_j`$, so it always takes a two-step edge. Because $`p_{j} \ge 1`$,

```math
\ell_j\ge f(v_j)+1>f(v_j).
```
The strictly increasing lengths $`p_{j}`$ give strictly increasing $`v_{j}`$. The formal endpoints are `matchLength_exceeds`, `starts_strict`, and `finite_match_exceeds`. No monotonicity of $`f`$ enters the argument.

## Why the limit is aperiodic

Suppose the limit were periodic with positive period $`p`$ from position $`N`$ onward. Choose stage $`j=N+p`$. Its block length satisfies

```math
M_j\ge p_j\ge j+1=N+p+1.
```
Set $`k=2M_{j}-p`$. Then

```math
N\le M_j\le k<2M_j,\qquad k+p=2M_j.
```
The stage contains a false bit at $`k`$ in its zero block and a true bit at $`k+p`$ at its final position. `target_zero_block` and `target_terminal_true` transfer those values to the limit. They contradict the alleged eventual period. `target_aperiodic` proves this for every pair $`(N,p)`$ with $`p>0`$.

Finally, `no_infinite_match` applies the already checked `BinaryAvoidance.aperiodic_target_avoided` theorem to this constructed word. This combines the diagonal argument and the long finite paths without assuming either aperiodicity or limit coherence as an external premise.

## Verification and scope

From the repository root in PowerShell:

```powershell
$env:ELAN_HOME = 'C:\Users\Owner\.elan'
$env:PATH = 'C:\Users\Owner\.elan\bin;' + $env:PATH
& 'C:\Users\Owner\.elan\bin\lake.exe' env lean lean/SamuelAlexanderResearch/SlowAvoidance.lean
```

The module compiles with Lean 4.33.1 in the existing Std-only project, exits successfully, and emits no warnings. Its seven selected `#print axioms` endpoints pass. The limit, periodic-prefix, aperiodicity, increasing-start, and finite-match endpoints use only `propext` and `Quot.sound`. The two endpoints importing the global no-infinite-match result also use `Classical.choice`. There are no `sorry`, custom axioms, `native_decide` endpoints, or Mathlib dependencies.

The result gives a target tailored to each supplied function $`f`$, with an infinite increasing family of starts exceeding that function's prescribed finite-match lengths. It does not assert that one target simultaneously exceeds every function, that all starting vertices satisfy the lower bound, or that a maximum-path-length function has been extracted as executable code. It also makes no time-complexity or formal computability-theory claim. The universal result and all indexing claims above are proved directly, rather than inferred from bounded scans.
