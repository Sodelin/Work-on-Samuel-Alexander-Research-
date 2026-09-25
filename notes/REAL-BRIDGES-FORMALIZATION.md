# Actual real birthdates and real-valued coefficient bounds

The optional [RealBridges](../real/RealBridges.lean) development uses actual
Mathlib real numbers, pinned to revision
`0df444a360eaa60ab8c11dca51a86af692955474`, with Lean 4.33.1. The default
combinatorial library remains Std-only. The [separate endpoint audit](../verification/real-audit.json)
records the dependency pin and source hashes.

## Population presentation

`BinaryRealPopulation V` has arbitrary vertex type $`V`$, infinitely many
vertices, actual real birthdates, finite lower sublevels, strictly increasing
dates along edges, one Boolean label per ordered pair, finitely many roots
and children per vertex, and an incoming parent for each Boolean label at
every nonroot. Finiteness is expressed by finite list covers and is connected
to Mathlib's `Set.Finite` by `finiteCover_iff_setFinite`.

`BirthOrder` constructs a bijection from the naturals in nondecreasing birth
order. It permits tied birthdates. The real adapter derives every natural
population hypothesis, proves root equivalence using surjectivity, applies
the proved positive theorem, and transports the path into $`V`$.
`eventuallyPeriodic_realized` thus has no supplied enumeration, countability
or positive-unavoidability conclusion as a premise. The original positive
theorem is Alexander's result, not a new classification claim.

The positive development specializes to the binary alphabet. A theorem for
every finite alphabet requires another generalization of the positive proof.

`binaryRealOfNat` assigns real birthdate $`v`$ to a natural vertex $`v`$ and proves
finite real sublevels using an Archimedean natural cutoff. It realizes the
negative $`P_{s}`$ witness inside the literal real model. Together with the positive
theorem, `binary_real_classification` gives the unconditional binary iff over
arbitrary small vertex types `V : Type`. The positive transport itself remains
universe-polymorphic.

`RealLabelledPopulation` specializes the independently checked
[PopulationReindex](../lean/SamuelAlexanderResearch/PopulationReindex.lean)
interface to actual real dates. The final wrappers prove subcritical
impossibility for every finite alphabet, an injective family `Fin k -> V` of
actual roots, and a lower bound $`k`$ on every root-cover list's length. The root
statement is a lower bound, not an exact count, and the generic adapter derives
all numerical counts and support bounds from the original local hypotheses.

## Sharp coefficients

`real_sharp_bound` rewrites the checked integer inequality as
$`\ell \le (\frac{8}{3})\cdot v - \frac{1}{3}`$. `real_coefficient_optimal` proves that for every real
$`c<\frac{8}{3}`$ and every real $`C`$, an actual positive-start maximum exceeds $`c\cdot v+C`$.
It uses the exact dyadic family and the Archimedean growth of powers of two.

The finite-edit and phase theorems prove the corresponding upper bounds
$`\ell \le (\frac{8}{3})\cdot v + (8\cdot m-1)/3`$ and
$`\ell \le (\frac{8}{3})\cdot v + (5\cdot a-1)/3`$, and the same real-coefficient optimality for
each fixed edit bound or phase. Maximum existence is part of the optimality
endpoints. Lower sharpness follows from actual arbitrarily late witnesses,
not merely from the upper bound.

These coefficients multiply the **natural vertex index cast to a real
number** in the particular graph $`P_{s}`$. They do not measure growth against
an arbitrary real birthdate map. Reparametrizing birthdates need not preserve
an index-based quantitative rate.

## Static convex geometry

A common point of two subsets of a real module belongs to their normalized
weighted mix: choose that same point in both summands and use $`a+b=1`$.
The proof holds without nonnegativity, hence covers convex weights too.
The final endpoint applies this inclusion to actual real convex hulls.
It proves neither infinite cellular-automaton lifeline existence nor velocity
convergence nor an improved speed limit for a particular rule.

## Reproduce

```sh
cd real
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
lake exe cache get Mathlib.Algebra.Order.Archimedean.Real.Basic Mathlib.Algebra.Order.Archimedean.Basic Mathlib.Analysis.Convex.Hull Mathlib.Tactic.Linarith Mathlib.Tactic.Positivity Mathlib.Tactic.NormNum Mathlib.Tactic.Ring
cd ..
python checks/audit_lean.py --real --output verification/real-audit.json
```

On this Windows host the toolchain's bundled curl could not negotiate its
TLS credentials. The optional [recovery helper](../real/fetch_cache_windows.py)
reads the official generated cache manifest, restricts downloads to the
official Mathlib cache hosts and hash filenames, uses verified system TLS,
bounded retries and atomic writes, and resumes completed downloads. It does
not disable certificate verification or alter global curl settings. After
downloads, ordinary `lake exe cache unpack` installs the cache. The Linux CI
uses the ordinary Mathlib cache command above.
