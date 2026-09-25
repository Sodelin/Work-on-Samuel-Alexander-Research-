# Attained finite maxima for every aperiodic target and start

[`FiniteAvoidance.lean`](../lean/SamuelAlexanderResearch/FiniteAvoidance.lean) closes the finite-maximum packaging boundary for the actual target-dependent graphs $P_{s}$. The main endpoint needs only a Boolean target $s$, a proof that $s$ is not eventually periodic, and a natural starting vertex $v$. It accepts no finite bound, compactness assumption, or assumed maximum. It includes $v = 0$.

## Exact predicates and proof chain

The module reuses the existing predicates without redefining their semantics:

- `BinaryAvoidance.Edge s u w b` is an actual edge of the row-colored +1/+2 construction, with the original missing edge $0 \to 1$ and destination condition $w \ge 2$.
- `QuantitativeAvoidance.MatchesPrefix s path ell` checks all first $\ell$ edges against the target's first $\ell$ symbols.
- `FiniteEditStability.HasPrefix s v ell` asserts existence of such an actual path function starting at $v$.
- `FiniteEditStability.IsMaximumPrefix s v ell` requires an attained length-$\ell$ witness and bounds every other witnessed finite matching length by $\ell$. Length zero is included.

`prefix_to_finitePath` converts an actual function-path prefix into `PositiveUnavoidability.FinitePath (Edge s) s 0 ell (path 0) (path ell)`. Induction appends the final edge with its original target phase, preserving both endpoints.

`aperiodic_endpoints_bounded` proves that the matching endpoints reachable from any fixed start are bounded. If they were unbounded, the already proved `PositiveUnavoidability.infinite_path_from_good` would construct an actual infinite matching path. Its finite-child hypothesis is supplied by `BinaryPopulation.children_finite s`, a theorem about the concrete graph. The resulting infinite path contradicts `BinaryAvoidance.aperiodic_target_avoided`. Thus the finite-branching argument and absence of an infinite match produce the bound as a conclusion.

`aperiodic_prefix_lengths_bounded` converts this endpoint bound to a bound on lengths. Every actual edge advances at least one index, so the existing finite displacement theorem gives $\operatorname{path}(0)+\ell\le\operatorname{path}(\ell)$. This is why bounded endpoints bound all possible matching lengths, not just the length of one selected path.

`aperiodic_maximum_exists` then applies the existing bounded finite maximum argument and proves:

```lean
∀ (s : Nat → Bool), ¬BinaryAvoidance.EventuallyPeriodic s →
  ∀ v, ∃ ell, FiniteEditStability.IsMaximumPrefix s v ell
```

`aperiodic_finite_extinction` gives the equivalent explicit endpoint: some length $\ell$ is attained, and every strictly longer actual matching prefix is absent. Both theorems cover every natural start, including roots and zero. They are classical existence results; they do not claim an effective procedure that extracts a bound from an arbitrary black-box target and a proof of aperiodicity.

## Slow avoidance now uses actual finite maxima

`arbitrarily_slow_finite_maxima` composes the preceding theorem with the frozen `SlowAvoidance.arbitrarily_slow_avoidance`. For every function `f : Nat → Nat`, it supplies:

1. an actual Boolean sequence $s$ that is not eventually periodic and has no infinite matching path in $P_{s}$;
2. an attained finite maximum at every starting vertex;
3. strictly increasing starting vertices `starts j`; and
4. for each $j$, an attained finite maximum $\ell$ at `starts j` with $f(\operatorname{starts}(j))<\ell$.

The final strict inequality follows because the previously constructed finite witness is no longer than the attained maximum. No monotonicity or computability assumption on $f$ is needed. This strengthens the earlier long-finite-witness statement with the missing maximum-existence assertion; it makes no claim about a uniform upper bound for all aperiodic targets.

## Verification and provenance

From the repository root with the existing Lean 4.33.1 toolchain:

```powershell
$env:ELAN_HOME = 'C:\Users\Owner\.elan'
& 'C:\Users\Owner\.elan\bin\lake.exe' env lean lean/SamuelAlexanderResearch/FiniteAvoidance.lean
& 'C:\Users\Owner\.elan\bin\lake.exe' build SamuelAlexanderResearch.FiniteAvoidance
```

Both checks pass without warnings. The source contains no `sorry`, `admit`, new axiom, or `native_decide`. The path-conversion theorem uses only `propext` and `Quot.sound`; the existence endpoints additionally use `Classical.choice` through the checked finite-branching argument and finite maximum selection.

The concrete avoiding graph and offset proof come from the [September 2026 classification manuscript, Section 2](https://github.com/avg-netizen/biological-unavoidability/blob/3d6175e3e23f67bd68e7be591b5a9a6d04e496a3/paper.md#2-an-explicit-binary-avoiding-population). The finite-branching proof is already formalized in `PositiveUnavoidability.lean`; this module applies it to close the repository's stated finite-extinction/maximum boundary. The slow-growth construction remains the one formalized in `SlowAvoidance.lean`. No source-priority claim is made for this packaging theorem.
