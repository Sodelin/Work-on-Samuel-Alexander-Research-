# Binary minimum crossing width forces a rigid tail

The checked module is [`MinimalCrossing.lean`](../lean/SamuelAlexanderResearch/MinimalCrossing.lean). It proves an equality-case theorem for the actual infinite graph counts developed in `InfiniteConservation.lean`. No edge pattern, eventual degree equality, alternating gender sequence, or word realization is assumed.

The population background is the infinite, finite-root, finite-child model in [Alexander's classification paper, Definition 1](https://arxiv.org/html/1212.0186v2). The results below are repository deductions, not claims that the paper states these cut-width theorems or that a literature-wide novelty search has been completed.

## Exact model and hypothesis

The main graph theorem takes `p : PopulationCounting.InfiniteLabeledPopulation 2 2`. Vertices are all natural numbers in strict birth order. Each ordered pair has at most one edge, encoded by `p.edge u v : Option Nat`. Every nonroot has a parent for each required label 0 and 1; these parents are distinct because one pair cannot carry two labels. Every source has an actual full outdegree at most two, with a finite support bound for every outgoing edge. All roots have indices below `p.rootSupport`.

Write `C_N` for `InfiniteConservation.crossingCount p N`: the full number of edges with source below `N` and target at least `N`. Every child is included in this count through its source's certified child-support bound. It is not an assumed aggregate or a count in a truncated ambient graph.

The rigidity hypothesis is explicit: there is a cutoff `start`, all roots are below it, and **`C_N = 3` for every `N ≥ start`**. This is the equality case of the previously proved universal binary lower bound `C_N ≥ 3` on root-free cuts. A single minimum-width cut suffices for the local conclusions below; the tail edge theorem needs the equality at every later cut.

## Checked conclusions and proof mechanism

1. `minimum_cut_columns` proves that, at one root-free cut of width three, exactly two edges enter vertex `N` from before the cut and exactly one enters vertex `N+1` from before the cut. The two required parents of `N` are both old; `N+1` can have at most one new parent. Their lower bounds exhaust the three crossing edges.
2. `minimum_cut_internal_edge` consequently proves the actual edge `N → N+1` exists. `minimum_cut_no_late_target` proves that **no source below `N` can have an edge to a target at least `N+2`**. The latter proof counts the first two target columns together with any proposed later target column and compares their sum with the actual full crossing count. Both local results work with any offspring cap `d`.
3. `regular_of_equal_crossing` uses full-degree conservation at `N` and `N+1`, stable roots, and equality of the two cut widths to prove zero local defect and exact full in/outdegrees two at `N`. There is no regularity premise or separately chosen eventual regularity threshold.
4. `minimum_tail_edges` proves, for every `u ≥ start` and every natural `v`,

   ```lean
   (p.edge u v).isSome = true ↔ v = u+1 ∨ v = u+2
   ```

   Apply the local no-late-target theorem at cut `u+1` to exclude jumps of length at least three. Strict birth order excludes nonforward edges. The full outdegree is two, so both remaining possible edges must exist. The conclusion holds from the supplied cutoff itself. `eventually_minimum_tail_edges` packages the version where the initial minimum-width cutoff has not been required to contain all roots.
5. `minimum_tail_parents` also proves that the **only** parents of `u+2`, for `u ≥ start`, are `u` and `u+1`. Its proof excludes earlier exceptional sources by applying the minimum-cut theorem at `u`.

## Fixed source genders and actual labelled paths

`genderBit false = 0` and `genderBit true = 1`. The additional hypothesis `FixedSourceGender p gender` says that every actual outgoing edge from `u` has label `genderBit (gender u)`. It is a permanent vertex-gender condition, not an assertion about which words are realized or which genders appear consecutively.

`minimum_tail_genders` proves

```lean
∀ u, start ≤ u → gender (u+1) = !(gender u)
```

The actual parents of `u+2` are the two consecutive vertices `u` and `u+1`; the population's required parents of labels 0 and 1 force their permanent genders to differ.

`minimum_width_realizes_above` constructs a path for every word `word : Nat → Bool`, starting above any requested natural bound. The initial vertex is chosen from two consecutive tail vertices so its gender matches `word 0`. At every step, the child at distance one or two is chosen so its gender matches the next symbol. Both edges are present by the proved rigidity theorem. The endpoint asserts the actual edge equations

```lean
∀ k, p.edge (path k) (path (k+1)) = some (genderBit (word k))
```

`binaryEdge p` is exactly this Option-to-Boolean relation. The module's `Realizes p word` is an abbreviation of `BinaryPopulation.Realizes (binaryEdge p) word`; no independent path semantics are introduced. `minimum_width_realizes_all` states universal realization given eventual minimum width and fixed source genders.

Finally, `avoiding_word_eventual_width_ge_four` proves that a fixed-source-gender critical binary population avoiding even one Boolean word has an **eventually constant crossing width at least four**. This uses the already proved eventual constancy of full crossing counts, the lower bound three, and the new universal realization result to exclude equality three.

## Verification and remaining scope

From the repository root, with Lean 4.33.1 selected by the existing toolchain:

```powershell
$env:ELAN_HOME = 'C:\Users\Owner\.elan'
& 'C:\Users\Owner\.elan\bin\lake.exe' env lean lean/SamuelAlexanderResearch/MinimalCrossing.lean
& 'C:\Users\Owner\.elan\bin\lake.exe' build SamuelAlexanderResearch.MinimalCrossing
```

Both checks pass. The module contains no `sorry`, `admit`, new axiom, or `native_decide`. The printed endpoint dependencies are only `propext`, `Classical.choice`, and `Quot.sound`.

The rigidity result here is binary. It does not classify tails at larger crossing width or prove the corresponding general-label equality case. Universal realization uses permanent source genders; the underlying +1/+2 edge pattern alone does not establish it for source labels that may differ between a vertex's outgoing edges. The theorem is formulated in the naturally ordered infinite population model; applying it to an arbitrary real-birthdate presentation uses the separate birth-order/real adapter. No claim that all critical two-child populations have width three, or that this resolves the full fixed-gender two-child question, is made.
