# Finite matching paths in the Thue–Morse avoiding population

**Status.** This note preserves the original quadratic proof and finite evidence for the population in Section 2 of [*A classification of biologically unavoidable sequences*](https://github.com/avg-netizen/biological-unavoidability/blob/main/paper.md) (10 September 2026). The two questions originally recorded below and the exact equality set are now resolved by the independently reviewed [sharp dyadic trajectory proof](../research/thue-morse/NEXT-INVARIANT.md) and its [full Lean implementation](../lean/SamuelAlexanderResearch/SharpThueMorse.lean). The checked proof includes actual bits, dyadic runs, the original-edge bridge, and finite maxima. The expanded [current audit](../verification/formal-audit.json) includes these endpoints and the later corollaries. No literature-priority claim is established.

## Definition

Write $`t(n)`$ for the parity of the number of 1s in the binary expansion of $`n`$. The population has vertex set $`\mathbb{N}`$. For each $`w \ge 2`$, its two incoming edges are

- $`w-1 \to w`$, with label $`t(w)`$;
- $`w-2 \to w`$, with label $`1-t(w)`$.

There is no $`0 \to 1`$ edge. A matching path starting at $`v`$ is a sequence $`v_0=v, v_1, \ldots, v_{l}`$ whose edge from $`v_{k}`$ to $`v_{k+1}`$ has label $`t(k)`$. Define $`L(v)`$ as the greatest possible $`l`$. The paper proves that $`L(v)`$ is finite, because $`t`$ is not eventually periodic. The result below supplies a numerical upper bound.

## Proposition: a quadratic bound

For $`v=2m`$, $`L(v) \le 2m^2 + 7m + 3`$. For $`v=2m+1`$, $`L(v) \le 2m^2 + 8m + 5`$. In particular, for every $`v \ge 0`$,

```math
L(v)\le\frac{(v+1)(v+6)}{2}.
```
**Proof.** For a matching path, put $`d_{k} = v_{k} - 2k`$. The paper's induction gives $`d_{k} \ge 0`$: it holds at $`k=0`$; if $`d_{k}=0`$, a one-step edge would enter $`2k+1`$ with label $`t(2k+1)=1-t(k)`$, so a matching edge must be a two-step. A two-step leaves $`d`$ unchanged, and a one-step decreases it by one. Thus the path has at most $`v`$ one-steps, and it visits each offset $`d`$ at most once, in one consecutive block.

Fix a block at offset $`d`$ and let $`q=\left\lfloor\frac{d}{2}\right\rfloor+1`$. A matching two-step at path index $`k`$ arrives at $`w=2k+d+2`$. If $`d=2e+1`$ is odd, $`w=2(k+e+1)+1`$, so the incoming edge has label $`1-t(w)=t(k+q)`$. Matching requires $`t(k)=t(k+q)`$. If $`d=2e`$ is even, $`w=2(k+e+1)`$, so matching requires $`t(k)=1-t(k+q)`$.

The Thue–Morse word is overlap-free: it has no factor of length $`2p+1`$ with period $`p>0`$. For odd $`d`$, $`q+1`$ consecutive two-steps would give $`t(i)=t(i+q)`$ at $`q+1`$ consecutive indices. This makes a factor of length $`2q+1`$ with period $`q`$, a contradiction. Hence at most $`q`$ two-steps occur at that offset.

For even $`d`$, suppose $`3q+1`$ consecutive two-steps occurred. Their relations $`t(i)=1-t(i+q)`$ imply $`t(i)=t(i+2q)`$ for $`2q+1`$ consecutive indices. This makes a factor of length $`4q+1`$ with period $`2q`$, again an overlap. Hence at most $`3q`$ two-steps occur at that offset.

For $`v=2m`$, summing over all possible offsets $`0,\ldots,2m`$ gives at most

```math
2m+3(1+\cdots+(m+1))+(1+\cdots+m)=2m^2+7m+3
```
edges: the first term bounds one-steps, and the others bound two-steps at even and odd offsets. For $`v=2m+1`$, the same sum is

```math
(2m+1)+4(1+\cdots+(m+1))=2m^2+8m+5.
```
The stated uniform bound is a looser expression that dominates both cases. QED.

**External premise.** Overlap-freeness is classical. A primary research publication by Jean Berstel and Patrice Seebold, *A characterization of overlap-free morphisms*, *Discrete Applied Mathematics* 46 (1993), 275–281, gives the definition and states Thue's theorem as Theorem 2.1; its Lemma 4.1 discusses preservation under the Thue–Morse morphism: https://igm.univ-mlv.fr/~berstel/Articles/1993OverlapFree.pdf . The quadratic argument above is not formalized in Lean here. Section 2 of the [classification repository](https://github.com/avg-netizen/biological-unavoidability/blob/main/paper.md) supplies the population and offset induction.

## Historical exact finite search

`explore.py` performs breadth-first search. At depth $`k`$, its set contains every endpoint of a path starting at $`v`$ whose first $`k`$ labels match $`t(0),\ldots,t(k-1)`$. It applies both outgoing edges and deduplicates endpoints. The first empty next frontier gives $`L(v)=k`$ exactly. The proved quadratic bound is an assertion guard: if it were exceeded, the program fails instead of reporting a truncated length. The computation does not certify the quadratic theorem; that rests on the proof above.

The set-frontier run is:

    python checks/explore.py --limit 8192 --output checks/scan-8192.json
    python -m unittest discover -s checks -p 'test_*.py' -v

The scan checks every starting vertex $`0 \le v < 8192`$. It reports no counterexample to the proposed linear bound $`3L(v) \le 8v-1`$ for $`v\ge 1`$. Equality occurs at exactly $`v=2, 5, 11, 23, 47, 95, 191, 383, 767, 1535, 3071, 6143`$ in this range. These are $`v=3\cdot 2^n-1`$ for $`0\le n\le 11`$, with $`L(v)=8\cdot 2^n-3`$. The largest computed value is $`L(6143)=16381`$. The JSON records each $`L(v)`$, so the summary can be recomputed without rerunning the search. For $`v=0,\ldots,15`$, the lengths are

```math
1,0,5,0,1,13,7,0,1,3,0,29,1,0,15,0.
```
The separate `bitset_probe.py` shifts a bitset of all reachable endpoints and intersects it with bit masks for the two labels. Its finite check stops at the proposed linear budget; if a frontier persisted beyond that budget, it would report a counterexample and a lower bound instead of asserting the conjecture. Run it with

    python checks/bitset_probe.py --limit 131072 --output checks/scan-bitset-131072.json.gz

This second implementation checked every start $`1 \le v < 131072`$. It found no counterexample. Thus every length in its output is exact. Equality occurs exactly at $`v=3\cdot 2^n-1`$ for $`0\le n\le 15`$ in that range; the largest length is $`L(98303)=262141`$. Its lengths for $`1\le v<8192`$ agree point-for-point with the set-frontier output. Both scripts check finite sets of starts and do not prove the linear bound.

An independent small-case test enumerates distinct path histories rather than merging endpoints. The six tests also compare both frontier implementations for all starts $`1\le v\le 255`$. These checks catch transition or stopping-index errors in that range; the larger computational agreement provides additional diagnostic evidence, not a proof of implementation correctness.

## Original conjectures and their resolution

The statements below were the conjectures motivating the search. The [constructive trajectory proof](../research/thue-morse/NEXT-INVARIANT.md) and [Lean sharp theorem](../lean/SamuelAlexanderResearch/SharpThueMorse.lean) now prove both, and `sharp_equality_indices` proves that the displayed family contains every equality start. The scans remain finite evidence and are not substituted for that argument.

1. **Global inequality:** $`L(v) \le \left\lfloor\frac{8v-1}{3}\right\rfloor`$ for every $`v\ge 1`$.
2. **Equality family:** $`L(3\cdot 2^n-1)=8\cdot 2^n-3`$ for all $`n\ge 0`$. The historical scans checked only $`n\le 15`$; the new proof covers every natural $`n`$.

The leading constant $`\frac{8}{3}`$ is optimal by the infinite equality family. Historically, the real-coefficient statement and the exact baseline $`H(v)`$ first-hit formula were recorded as prose corollaries. They are now checked in [RealBridges](../real/RealBridges.lean) and [SharpCorollaries](../lean/SamuelAlexanderResearch/SharpCorollaries.lean), respectively; the bound, finite maxima, equality family, and exact equality classification are also exported Lean endpoints. See the [current formalization coverage](../FORMALIZATION.md). The sharp proof combines exact interval frontiers with dyadic blocks of boundary advances. The older overlap-free argument above remains valid but gives a weaker numerical bound.

For a small reproducible check of the sharp proof's indexing, run `python research/thue-morse/sharp_check.py`. It passes 18 full trajectory replays, 8,140 advance comparisons, and 256 bounded first-hit checks, and compares the inequality and exact equality set with the saved 8,192-start scan. Its output is finite corroboration, not the basis of the universal proof.

The calculation in this historical note concerns the exact edge-labelled $`P_{t}`$ population and paths matching the Thue–Morse sequence from index zero. Later [PhaseShift](../lean/SamuelAlexanderResearch/PhaseShift.lean) and [PhaseExtremal](../lean/SamuelAlexanderResearch/PhaseExtremal.lean) treat shifted targets together with their rebuilt graphs. The calculation here makes no claim about other avoiding populations or physical biological systems.
