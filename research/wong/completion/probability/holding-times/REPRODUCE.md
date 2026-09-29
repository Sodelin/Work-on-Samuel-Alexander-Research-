# Reproduce the waiting-time result

Use the repository at the exact proof commit named in [PUBLICATION.json](PUBLICATION.json). The canonical source is [real/WongWaitingTimes.lean](../../../../../real/WongWaitingTimes.lean). The worker copy and original receipts preserve the earlier local check.

From a fresh checkout with the repository's pinned Lean toolchain available:

```sh
lake build
cd real
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
lake exe cache get Mathlib.Probability.Distributions.Exponential Mathlib.Probability.ProductMeasure Mathlib.Probability.Independence.InfinitePi Mathlib.Probability.Independence.Basic Mathlib.Probability.CDF Mathlib.Data.Nat.Find Mathlib.MeasureTheory.MeasurableSpace.Constructions Mathlib.MeasureTheory.Constructions.BorelSpace.Order Mathlib.Tactic.Linarith Mathlib.Tactic.Positivity Mathlib.Probability.Kernel.IonescuTulcea.Traj Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
lake build WongWaitingTimes
lake env lean WongWaitingTimes.lean
cd ..
```

For the complete repository audit, follow [.github/workflows/verify.yml](../../../../../.github/workflows/verify.yml). It supplies the union of exact Mathlib cache roots used by the real library and runs the core, real and standalone audits. The waiting-time addition extends the real endpoint manifest by 24; the complete expected real total is 317.

Required pins: Lean 4.33.1; Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. Each of the 24 selected waiting-time declarations must report only `propext`, `Classical.choice` and `Quot.sound`. A build alone does not replace the separate statement/source review.

The historical local check used one compiler worker, a 4096 MB memory limit, and officially acquired Mathlib cache objects. The frozen prerequisites were rebuilt in an isolated worker directory. No failed development logs or compiled objects are required for the published reproduction.

The review's local XML locator and historical relative paths describe its original workspace. The publication record maps the frozen count and absorption sources to their canonical repository locations.
