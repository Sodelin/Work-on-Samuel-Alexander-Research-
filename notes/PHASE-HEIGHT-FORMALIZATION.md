# Exact effective heights at every Thue–Morse phase

`PhaseHeight.height_isMaximum a v` proves an attained finite maximum in the
actual graph built from the shifted target `t_a(k)=t(k+a)`, for every phase
`a` and start `v`, including `v=0`. `PhaseHeight.height` is a computable finite
algorithm, rather than an arbitrarily chosen maximum or an assumed bound.

## Actual finite frontiers

`successors s k x` filters the only two possible destinations, `x+1` and
`x+2`, by the actual predicate `BinaryAvoidance.Edge s x y (s k)`. The graph's
destination condition `y>=2` is included, so the nonexistent edge `0 -> 1`
is never admitted.

`frontier s v 0` is `[v]`; each subsequent frontier concatenates the valid
successors of the preceding frontier. `mem_frontier` proves that list
membership is equivalent to existence of an actual function-path prefix
with the specified start, length, and endpoint. `hasPrefix_iff_frontier_nonempty`
then identifies nonemptiness with the existing `HasPrefix` predicate.

`boundedHeight s v b` checks matching lengths down from `b`, returning the
largest successful length. `boundedHeight_isMaximum` proves correctness
when `b` bounds all actual matching lengths. It includes length zero, which
always has a witness.

## Derived bound and maximum

The required bound is derived, not supplied to the phase-height endpoint.
Translate a shifted prefix up by `2a` and prepend the original first `a`
target bits using the already checked `PhaseShift.prepend_shifted_prefix`.
The resulting original start lies in `[v,v+a]`.

If that start is positive, the proved sharp Thue–Morse prefix bound applies.
If it is zero, the separately checked original zero-start maximum is one.
Both cases imply the deliberately loose, uniform bound

```math
\ell\le8(v+a)+1.
```

`height a v` is `boundedHeight` evaluated at this derived bound.
`height_isMaximum`, `hasPrefix_iff_le_height`, and `maximum_iff_height` prove
that it is exactly the maximum of all actual matching prefixes, with no
positive-start restriction or supplied compactness premise.

This is an exact finite algorithm and a useful interface for finite edits.
It is not a new closed-form formula in `(a,v)`, a logarithmic digit algorithm
for arbitrary phases, or an optimization of the previously proved sharp
phase-dependent inequality. Those distinctions matter: finiteness makes
the present procedure effective, but no runtime complexity bound is proved.
The phase-zero digit formula is handled independently in `FullHeight` and
`DigitRecurrence`.

## Verification

With `ELAN_HOME=C:/Users/Owner/.elan`, from the repository root:

```text
lake env lean lean/SamuelAlexanderResearch/PhaseHeight.lean
lake build SamuelAlexanderResearch.PhaseHeight
```

Both checks pass. Printed endpoints use only the standard axioms `propext`,
`Classical.choice`, and `Quot.sound` (some use a subset). There are no
`sorry`, `admit`, custom `axiom`, or `native_decide` declarations.
