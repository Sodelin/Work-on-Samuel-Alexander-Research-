# Finite-state periodicity: Lean verification receipt

Date: 2026-09-25.

## Frozen source

Module: `work/repo/lean/SamuelAlexanderResearch/FiniteStatePeriodicity.lean`.

SHA256: `783886827f5a819bee91b87392f697ddf96901f320cf5b3b9ee5d29f77a0642d`.

Only this new Lean module was created. No existing Lean module was edited; no commit or publication was made by this helper task.

## Statement and assumptions

For arbitrary $`q\in\mathbb N`$, a fixed transition $`\mathrm{step}:\mathrm{Fin}(q)\to\mathrm{Fin}(q)`$, and an orbit $`f:\mathbb N\to\mathrm{Fin}(q)`$, the sole dynamical premise is

```math
\forall n\in\mathbb N,\qquad f(n+1)=\mathrm{step}(f(n)).
```

The theorem derives

```math
\exists N,p\in\mathbb N,\qquad
p>0\ \land\ \forall n\ge N,\quad f(n+p)=f(n).
```

There is no recurrence or eventual-periodicity hypothesis. An orbit itself entails that the state space is nonempty; consequently a separate positive-state-count hypothesis is unnecessary. The proof first derives two equal states at distinct times using finiteness, then propagates their equality by determinism.

`observed_eventually_periodic` also derives eventual periodicity after applying any time-independent observation function to the states. The label type of that observation is arbitrary.

## Compiler result

Command, run in `work/repo` with `ELAN_HOME=C:/Users/Owner/.elan`:

```powershell
lake env lean lean/SamuelAlexanderResearch/FiniteStatePeriodicity.lean
```

Exit code: **0**. No warnings or errors. Compiler: **Lean 4.33.1**, Windows GNU build, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. Import: `Std`.

| Endpoint | Line | Reported axioms |
|---|---:|---|
| `FiniteStatePeriodicity.repeated_state` | 50 | `propext`, `Classical.choice`, `Quot.sound` |
| `FiniteStatePeriodicity.equal_at_offset` | 70 | None |
| `FiniteStatePeriodicity.eventually_periodic` | 80 | `propext`, `Classical.choice`, `Quot.sound` |
| `FiniteStatePeriodicity.observed_eventually_periodic` | 93 | `propext`, `Classical.choice`, `Quot.sound` |

No `sorry`, `admit`, or custom axiom declarations occur in the source.

## Scope

This is a standard finite-state result, with no priority claim. Applying it to a population encoder requires a genuinely finite state representation and a deterministic, time-independent transition on that state. A finite graph of legal updates permitting arbitrary nondeterministic choices does not meet that premise. Likewise, time-dependent output labels are not covered merely because the underlying state orbit is periodic.

This receipt verifies the isolated helper module. It does not certify the population encoder, the entire repository build, or any publication state.
