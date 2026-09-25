# An upper bound from failures of periods and antiperiods

**Status: proved in Lean.** See [QuantitativeModulus.lean](../lean/SamuelAlexanderResearch/QuantitativeModulus.lean). Together with the existing arbitrarily-slow lower construction, this resolves the modulus-to-bound target in proposal 6.

All paths are actual finite matching paths in the manuscript's own-target graph $`P_s`$. For a path starting at $`v`$, its nonnegative offset at time $`i`$ is

```math
d_i=\operatorname{path}(i)-2i.
```

Each edge leaves this offset unchanged or reduces it by one. A constant offset $`d`$ can take a two-step edge at time $`i`$ only if

```math
s(i)=\neg\operatorname{row}_s(2i+d+2).
```

Call failure of this equality a **break**. This condition is expressed only in target bits, independently of any matching path. For $`d=2e`$ a break is $`s(i+e+1)=s(i)`$, a failure of antiperiod $`e+1`$. For $`d=2e+1`$ it is $`s(i+e+1)\ne s(i)`$, a failure of period $`e+1`$.

## The explicit bound

A modulus $`M(v,b)`$ supplies, for every $`d\le v`$, a breaking index in the interval $`[b,M(v,b))`$. Define an executable clock from this supplied modulus by

```math
B_0=0,\qquad B_{r+1}=M(v,B_r).
```

Then every actual matching prefix of length $`\ell`$ from $`v`$ satisfies

```math
\ell<B_{v+1}.
```

If each such window has length at most a uniform $`R`$, namely $`M(v,b)\le b+R`$ for all $`b`$, the simpler bound is

```math
\ell<(v+1)R.
```

This is a bound from a specific word's failure-of-periodicity data. It does not assert a universal rate for all aperiodic words. The existing slow-avoidance theorem proves that no such word-independent rate can exist.

## Why it works

The offset is initially $`v`$ and cannot increase. Within each complete modulus window, apply the break condition to the offset at the window's beginning. If the offset did not decrease anywhere in that window, it would still have that value at the breaking index and the following step. The path would then be forced to take the forbidden two-step edge, a contradiction. Thus each full window consumes at least one unit of offset. A path cannot traverse $`v+1`$ such windows.

Every non-eventually-periodic target has a modulus of this form. If an offset never had a break beyond some point, odd offsets would give an eventual period directly, and even offsets would give an eventual antiperiod and therefore a doubled period. For each finite family of offsets, choose a break beyond the requested start and take a common finite window containing them.

The Lean existence proof uses classical choice for these witnesses. Given a supplied modulus, the clock and bound are explicit. For an effectively evaluable aperiodic word, searching for each local break is also a terminating relative procedure, but a separate computability predicate is not formalized here.

## Checked endpoints

- `aperiodic_has_break` and `aperiodic_has_modulus` derive the bit-based witnesses.
- `even_break_iff` and `odd_break_iff` identify the period/antiperiod tests exactly.
- `window_forces_drop` derives a decrease of the actual path offset.
- `prefix_length_lt_clock` bounds every finite matching prefix.
- `prefix_length_lt_uniform_windows` gives the product bound.
- `aperiodic_explicit_bounds` packages one modulus valid for every starting vertex.

The direct Lean check passes with only standard Lean axioms. In particular, no matching-length estimate or conclusion-equivalent graph property is assumed as part of the modulus.
