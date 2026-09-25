# The stateful CA comparison in literal real convex hulls

`real/StatefulCAReal.lean` closes the real-geometry representation gap for the
static comparison in `StatefulCA.lean`. It proves the exact east support value
over Mathlib's full `convexHull ℝ`, including points requiring irrational
weights, and combines this with the existing actual cellular-automaton
trajectory obstruction. The rule remains the synthetic three-state example
described in [STATEFUL-CA-FORMALIZATION.md](STATEFUL-CA-FORMALIZATION.md).

## Real sets and exact optimum

For each of the six directions, `vector d : ℝ × ℝ` is the componentwise cast
of the core's rational predecessor-to-child displacement
`(xStep d, yStep d)`. Thus the vectors are

```math
(1,0),\ (1,-1),\ (1,1),\ (-1,0),\ (-1,-1),\ (-1,1).
```

For a fixed label set `D`, `directionSet D` is the image of those directions
under `vector`, and `hull D` is literally

```lean
convexHull ℝ (directionSet D)
```

The checked endpoint `static_east_support_one` states that every valid static
two-label certificate `FixedCert a b` satisfies

```lean
IsGreatest ((fun v : ℝ × ℝ => v.1) '' (hull a ∩ hull b)) 1
```

This includes attainment. `static_east_optimum` exposes its two ingredients:
`(1,0)` belongs to both real hulls, and every point in their intersection has
horizontal coordinate at most one.

The lower witness uses the core's universally quantified local-certificate
lemma. For each label set, either direction zero belongs to the set, or both
directions one and two do. The first case puts `(1,0)` directly in the hull.
The second case puts it there as the midpoint of `(1,-1)` and `(1,1)`, using
Mathlib's convexity theorem. The upper bound uses the convex half-plane
`{v | v.1 ≤ 1}`: it contains every possible direction vector, so minimality of
the real convex hull puts the entire hull inside it. This upper proof is not
restricted to rational barycentric witnesses.

The adapter proves the real static endpoint directly. It does not add a
generic theorem embedding every `InConv D v` witness into a real hull; that
extra conversion is unnecessary for the universally quantified, attained
real optimum proved here.

## Actual trajectory bridge and independent audit

`real_horizontal_spaceship_speed_zero` applies the core theorem
`no_horizontal_spaceship`. For every finite nonempty initial configuration,
any exact recurrence of an iterate as a translate has horizontal displacement
zero. Casting that displacement to the reals gives zero horizontal velocity
for every positive period. The formal quotient identity also covers period
zero, since the stronger integer-displacement theorem already applies there.

`real_static_gap_and_global_obstruction` bundles:

- the valid aligned/diagonal static certificate;
- real east support exactly one for every valid static certificate;
- the actual rule's zero horizontal spaceship velocity for finite nonempty
  initial support;
- the finite domino configuration and its two complete generation updates.

The independent read-only audit checked the core at SHA-256
`F02F2B808A0C15D85B26C55559B54621599E89A04C44957679612F24BD4C9BBA`.
`FixedCert` quantifies over every live-output local row and requires two
distinct live parent directions, with the fixed label sets independent of
the row and state. Directions are predecessor locations; the cast vectors
have the correct predecessor-to-child signs. The global charge-strip
theorems concern the actual `evolve` and `iterate` functions and do not assume
the existence of a supplied infinite lifeline. The spaceship theorem allows
arbitrary vertical displacement and requires exact equality of configurations,
including their states. The finite nonempty support hypotheses are explicit.
The full two-cycle theorem checks the entire configurations, including absence
of any extra births.

No material statement or model-bridge defect was found. The static support
point at speed one is a limitation of this certificate family; it is not a
claim that the actual rule has a spaceship at that speed. The stateful theorem
excludes such a nonzero horizontal spaceship displacement.

## Build and integration

The new optional module imports only:

```lean
Mathlib.Analysis.Convex.Hull
Mathlib.Data.Real.Basic
Mathlib.Tactic.Linarith
Mathlib.Tactic.NormNum
SamuelAlexanderResearch.StatefulCA
```

It does not require `Mathlib.Analysis.Convex.Combination` or a further cache
fetch. From the repository's `real` directory:

```powershell
lake env lean StatefulCAReal.lean
```

The direct check passed without errors or warnings. The selected axiom
reports for `static_east_optimum`, `static_east_support_one`, and
`real_static_gap_and_global_obstruction` contain only `propext`,
`Classical.choice`, and `Quot.sound`. The module adds no axiom, admitted proof,
or native decision endpoint. No core module or real-project configuration was
changed by this adapter lane.
