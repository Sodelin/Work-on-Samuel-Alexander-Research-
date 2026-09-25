# A decidable subclass for universality of the binary witness family

**Status:** direct corollary of cited results; not a new general decidability theorem or a priority claim.

The classification manuscript's Section 5 considers its specific binary population `P_s`, built from a binary target sequence `s`. It states and argues that

```text
P_s realizes every binary infinite sequence  iff  s is eventually periodic.
```

Allouche, Rampersad, and Shallit give a proof of Honkala's theorem that eventual periodicity is decidable for a `k`-automatic sequence supplied by a finite automaton with output. Therefore, when the input for `s` is such an automaton, one can decide whether the **particular constructed graph** `P_s` is universal: decide whether `s` is eventually periodic, then apply the displayed equivalence.

The input restriction matters. The classification manuscript gives halting reductions for arbitrary programs describing sequences, so this corollary does not decide universality for every computable `s`, and it does not decide universality for an arbitrary population graph. No implementation or Lean formalization is included here.

Sources: [classification manuscript and source repository](https://github.com/avg-netizen/biological-unavoidability), Section 5; [Allouche–Rampersad–Shallit, *Periodicity, repetitions, and orbits of an automatic sequence*](https://arxiv.org/abs/0808.1657), abstract and main decidability result.
