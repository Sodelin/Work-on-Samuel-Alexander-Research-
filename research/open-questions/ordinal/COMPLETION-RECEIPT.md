# Checked ordinal rank and first-limit pruning

Date: 25 September 2026. These files close the previously written-only
ordinal-root calculation for the existing `BinaryNatPopulation` model.
The proof modules listed below are frozen at the hashes in `SHA256SUMS.txt`.

## Result and exact scope

For every existing binary natural-date population $`P=(\mathbb N,E)`$ and
binary target $`s`$ which $`P`$ avoids, the code proves the actual Mathlib
ordinal rank of its matching-history tree:

```math
\operatorname{rank}(\varnothing)=\omega,
\qquad
\operatorname{rank}(h)=H(h)\in\mathbb N
\quad\text{for every nonempty history }h.
```

Here $`H(h)`$ is the attained maximum number of further matching edges from
the history's endpoint and phase, constructed from actual avoidance in
`ReachableRankNecessity.lean`. It is not an externally supplied height or
bound.

`History` records a finite path by its length and a path function required to
be constant after its endpoint. Thus it retains the complete matching
history, not merely its endpoint and phase. `Child` appends one actual
matching edge. `Node` adds an artificial root whose children are exactly
the histories of length zero. `ordinalRank` is Mathlib's `Acc.rank` applied
to the proved accessibility of this `Below` relation.

The population link is internal. `finite_word_occurs` reuses the checked
`PositiveUnavoidability.backward_word` theorem and finite roots to prove
that every prescribed finite prefix occurs. It supplies the lower bound on
the artificial root. Actual avoidance plus finite branching supplies the
finite ranks of the nonroot histories. No cofinality, unboundedness, compactness,
or continuation-bound statement is an endpoint premise.

The pruning code also proves:

```math
\varnothing\in D^n\quad(n\in\mathbb N),
\qquad
D^\omega=\bigcap_{n\in\mathbb N}D^n=\{\varnothing\},
\qquad
D^{\omega+1}=\varnothing.
```

`survives` implements finite leaf-pruning by retaining a node precisely when
it has a surviving child. `atOmega` is explicitly the intersection of these
finite derivatives, and `atOmegaSucc` applies the same retention operation
once more. These are the concrete first-limit and successor stages; the
module does not build a general transfinite derivative library.

## Import and compile order

1. `ReachableRankNecessity.lean` imports the existing cached
   `SamuelAlexanderResearch.LayeredUnavoidability` module. This is an
   unchanged local copy of the prior proved necessity module.
2. `HistoryWellFounded.lean` imports `ReachableRankNecessity`.
3. `OrdinalHistoryRank.lean` imports `HistoryWellFounded` and
   `Mathlib.SetTheory.Ordinal.Rank`.
4. `HistoryPruning.lean` imports `HistoryWellFounded`; it can be checked
   immediately after step 2 independently of step 3.
5. `HistoryConverse.lean` imports `HistoryWellFounded` and can likewise be
   checked immediately after step 2.

The successful direct commands used `-o` to place each same-name `.olean`
in this isolated scratch directory. `LEAN_PATH` included this directory,
the owning checkout's `.lake/build/lib/lean`, its `real/.lake/build/lib/lean`,
and each directory `real/.lake/packages/*/.lake/build/lib/lean`.

Compiler:

```text
Lean (version 4.33.1, x86_64-w64-windows-gnu, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)
```

Mathlib revision from the owning `real/lake-manifest.json`:

```text
0df444a360eaa60ab8c11dca51a86af692955474
```

The root task acquired only the pinned cache closure requested by
`Mathlib.SetTheory.Ordinal.Rank`; it reported 894 cache files and exit code 0.
No Lean or Mathlib revision was changed.

## Compilation and exact axiom reports

All five source files compiled successfully with exit code 0. The actual
ordinal-rank module emitted three deprecation warnings for
`Ordinal.natCast_succ`, which remains available in this pinned Mathlib.
There were no proof errors or admitted propositions.

There are **17 printed endpoints**: six in the unchanged prerequisite and
eleven in the four new modules. The new endpoints are:

```text
'HistoryWellFounded.below_wellFounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'HistoryWellFounded.finite_word_occurs' depends on axioms: [propext, Quot.sound]
'HistoryWellFounded.population_heights_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'OrdinalHistoryRank.history_rank_eq_height' depends on axioms: [propext, Classical.choice, Quot.sound]
'OrdinalHistoryRank.root_rank_eq_omega' depends on axioms: [propext, Classical.choice, Quot.sound]
'OrdinalHistoryRank.aperiodic_Ps_root_rank_eq_omega' depends on axioms: [propext, Classical.choice, Quot.sound]
'HistoryPruning.root_survives_every_finite_stage' depends on axioms: [propext, Quot.sound]
'HistoryPruning.omega_stage_iff_root' depends on axioms: [propext, Classical.choice, Quot.sound]
'HistoryPruning.omega_succ_stage_empty' depends on axioms: [propext, Classical.choice, Quot.sound]
'HistoryConverse.wellFounded_below_excludes_realization' depends on axioms: [propext, Quot.sound]
'HistoryConverse.below_wellFounded_iff_avoids' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The unchanged prerequisite reports:

```text
'ReachableRankNecessity.reachable_endpoints_bounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'ReachableRankNecessity.reachable_maximum_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'ReachableRankNecessity.rank_isCertificate' depends on axioms: [propext, Classical.choice, Quot.sound]
'ReachableRankNecessity.rank_is_least' depends on axioms: [propext, Classical.choice, Quot.sound]
'ReachableRankNecessity.avoids_iff_has_natural_certificate' depends on axioms: [propext, Classical.choice, Quot.sound]
'ReachableRankNecessity.aperiodic_Ps_has_natural_certificate' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No printed endpoint depends on `sorryAx`. These proofs use only the standard
axioms shown above.

## Remaining gates and interpretation

- **Schmidt rank and its kernel:** remain written proofs. No Schmidt-rank
  implementation or new structure theorem is supplied by these modules.
- **Full source alphabet and date generality:** the actual ordinal and
  pruning modules presently use the existing binary, natural-date population
  definitions. A separate generic natural-certificate theorem can broaden
  certificate coverage without automatically broadening these ordinal modules.
- **No silent reduction to binary:** a population with an arbitrary finite
  label alphabet cannot simply be declared binary. A binary encoding would
  need a specified word code and graph construction, preserve the relevant
  population axioms, and address synchronization and paths beginning inside
  a codeword. Directly parameterizing the history/rank proof by the label
  type is an alternative; neither adapter is implemented here.
- **Converse formulations:** the prior natural-certificate equivalence is
  checked. These new modules prove avoidance implies well-founded histories
  and the displayed ranks/pruning stages. `HistoryConverse.lean` additionally
  proves `WellFounded Below` iff actual avoidance, by extending an actual
  infinite realizing path inside well-founded induction. The fixed-point
  pruning statement for realizing populations remains outside these modules.
- **Interpretation and novelty:** the root rank collapses to $`\omega`$ for
  every avoider in this model. This exact membership invariant does not
  supply a hierarchy distinguishing different avoiding populations. The
  formal proof is not a historical priority or independent endorsement claim.

Only the assigned scratch directory was edited. Owning source files and
publication branches were unchanged by this lane. Compiled `.olean` files
are local verification outputs; the `.lean` sources and receipt are the
reviewable artifacts.
