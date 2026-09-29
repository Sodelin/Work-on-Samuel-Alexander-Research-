# Sol2 adversarial review — Wong probability cycle

Input: PROBABILITY-STATEMENT-BRIEF.md and selected-statements.txt, read before proof bodies. Scope: 19 selected local endpoints; no compiler run, no source edit, no public receipt claim.

## Counterexample attempts recorded before proof inspection

1. **Wrong normalization:** at a=b=1 and k=2, the literal split and merge rates are 2 and 1, so the upward jump mass must be 2/3. If normalizedRatio is b/a, the displayed literal mass theorem is false. Check exact casts and k=j+2 indexing.
2. **Boundary b=0:** with a>0, all k≥2 jumps must go down. Any positivity assumption b>0 or denominator cancellation through b would silently exclude this valid case.
3. **Totalization versus biological starts:** n=0 must go to 1 in one jump and incur one transient step, while n=1 is already absorbing and has zero transient cost. Positive starts should never reach 0. Challenge the all-k drift endpoint separately at k=0 and k=1.
4. **Quantifiers:** for θ>0 a trajectory can keep jumping upward indefinitely as an element of path space, even if that set has probability zero. “Almost every eventually 1” must not become every trajectory, a deterministic jump bound, or physical-time termination.
5. **Model scope:** count paths alone do not provide holding times, nonexplosion, spatial/genomic marks, or the projected law of a full ARG. A finite potential bound need not be the source's exponential expected-event asymptotic.

The attempts above were resolved against the pinned definitions and source below.

## Resolution against the pinned declarations

**Rates and boundaries.** `WongCountChain.transition` maps 0 and 1 to `dirac 1`; for `k=j+2` it puts only `θ/(θ+j+1)` on `j+3` and `(j+1)/(θ+j+1)` on `j+1`. `probabilities_sum`, `jump_up_mass`, and `jump_down_mass` identify the actual kernel masses. `literal_rate_ratio` and `literal_merger_ratio` assume `a>0, b≥0, k≥2`; `normalizedRatio_value` is exactly `θ=2b/a`. Thus at `a=b=1,k=2` the upward mass is `2/3` and the downward mass `1/3`, not `1/2`. At `b=0`, `θ=0`, so every `k≥2` descends with mass one. The positive denominator comes from `a>0` and `k≥2`, not from any assumption `b>0`.

**Zero, one, and positive starts.** `one_absorbing` fixes state 1. `countPotential N 0=1` and `countPotential N 1=0`; `countPotential_drift` explicitly branches on `k=0`, `k=1`, and `k=j+2`, paying cost `if k=1 then 0 else 1`. The two Dirac boundary inequalities are therefore distinct: `V(1)+1≤V(0)` and `V(1)+0≤V(1)`. `ae_positive_counts` assumes `n≠0` and shows almost-sure positivity at every jump; the `n=0` theorem instance is a disclosed totalization rather than a biological positive-start result. The literal-rate endpoint starts at `n+2`, so it never relies on that totalization.

**Constructed law and no hidden final premise.** `pathLaw θ n` is defined using `Kernel.traj` from `historyKernel`, and `initial_lintegral` and `step_lintegral` derive initial and one-step integral identities for this law. `sum_transient_le` and `ae_finite_absorption_of_drift` are openly conditional on a finite potential/all-state drift; they telescope transient probabilities and use a finite-sum eventuality theorem. The final `ae_eventually_one θ n` has only `θ : ℝ≥0` and `n : ℕ` as inputs: its proof selects a natural `N≥θ` by Archimedeanity and supplies `countPotential N` plus `countPotential_drift` internally. `countPotential` is finite at every state, with scalar drift from `weighted_gap`/`potential_drift` for positive excess count. `ae_finite_jump_absorption` and `literal_rates_ae_finite_absorption` are consequences, with no drift or absorption assumption in their final statements.

**Quantifier challenge.** `∀ᵐ ω` means almost every path, not every element of `ℕ→ℕ`. When `θ>0`, an infinite upward-only path belongs to that ambient space and is consistent with each allowed jump, although the event has measure zero. The statements give no deterministic upper bound on the number of jumps. State 1 is stopped; the packet does not model a stationary process continuing to split from count one.

## Source correspondence and limits

The pinned source XML `source/PMC11373519-fullText.xml` has SHA-256 `2b77c349f39d2885b3e36d3bcab639a7ef3b9c6217263031aa4bc8f1c2a0d05e`. Appendix B `app2`, paragraph 5 describes Big ARG mergers at `choose(k,2)`, recombinations at `kρ`, and stopping at one lineage with a finite-time claim. The formal rate identity specializes to `a=1,b=ρ` and therefore `θ=2ρ`; any comparison to the source's event-cost asymptotic in paragraph 6 must state this normalization and requires a separate expected-event analysis. The proof concerns the embedded **jump index**. To justify finite physical stopping time, one must construct the rate-dependent continuous holding times and their joint law with the count process; to claim an ARG result, one must construct the marked spatial process and verify its count projection. Neither construction is in these 19 endpoints. The source's finite-time and event-complexity language is therefore broader than the formal conclusion, without invalidating that conclusion.

`SOURCE-MANIFEST.json` matches the SHA-256 hashes of all three pinned source files and three logs. Its 19 reported selected endpoint axiom lists contain only `propext`, `Classical.choice`, and `Quot.sound`. The logs show only nonfatal linter/deprecation warnings; the handoff reports exit 0. I did **not** run Lean independently or certify public integration/CI.

**PASS WITH SCOPED LIMITS.** No listed counterexample refutes a selected declaration under its hypotheses, and the final endpoint does not assume its conclusion through a hidden drift premise. The actionable reporting boundary is to call this almost-sure finite **jump-count** absorption of the stopped embedded chain, not yet finite physical time, a spatial-ARG projection, or the source's expected-event asymptotic.
