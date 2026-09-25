# Proof structure and remaining obligations

## Where the research stands

We have completed **three precisely stated subproblems**: two have checked Lean proofs, and one has a written general proof supported by exact finite computation. **None of the twelve broader questions in the source paper is recorded as fully solved.** This distinction tells us what can be reused now and what still needs a mathematical definition, a proof, or empirical evidence.

This map follows the [twelve-question inventory](README.md). The source is Abramsky et al., *Open questions about time and self-reference in living systems*, [DOI 10.1098/rsos.261059](https://doi.org/10.1098/rsos.261059), published PDF SHA-256 `8b3940d8ac53c7145584c38c1a95a27c87f9c8173323112865c5439862bf43ce`. Page numbers below are from that published PDF. The questions are paraphrased; Q01–Q12 are our inventory identifiers.

The machine-readable counterpart is [problem-ledger.json](problem-ledger.json). It records source question → precise specification → proof obligations → evidence → residual gap. A proof obligation below is a stated mathematical task, not a Lean placeholder or an assumed axiom.

| Target | Completed precise result | Evidence | Broader source question |
|---|---|---|---|
| Q04: projection | Exact deterministic abstraction criterion; uniqueness; preservation of trajectories under the same controls; explicit rule-hiding obstruction | Checked Lean | Open beyond the selected preservation contract |
| Q09: changing players | Current membership alone cannot determine a predecessor-restoring split for both explicit legal merge histories | Checked Lean; separate pinned operator test with declared mocks | Open as a theory of games with changing players |
| Q12: calibration | Sharp error bounds for distinguishing an impossible branch from a known rare independent branch | Written proof; rational finite computation; independent review | Open for general evolutionary model calibration |

## Q04 — when projection loses the next-step dynamics

**Source:** §4.2, PDF p.11 asks whether the process of producing a result can always be separated from that result by projection. Our interpretation specifies what the projection must preserve: exact deterministic next observations under each allowed control. The projection itself exists; it may fail to support a closed deterministic update.

### Precise specification

Let $`A`$, $`X`$, and $`Z`$ be arbitrary types of controls, concrete states, and observations. Assume a deterministic update $`F:A\to X\to X`$ and a surjective observation $`c:X\to Z`$. Then:

```math
\left[\exists \bar F:A\to Z\to Z\;\;\forall a,x,\quad
c(F(a,x))=\bar F(a,c(x))\right]
\iff
\left[\forall a,x,y,\quad c(x)=c(y)\Longrightarrow c(F(a,x))=c(F(a,y))\right].
```

The right side says that concrete states with the same observation must have the same next observation under the same control. When it holds, the abstract update is unique on $`Z`$, and it preserves every finite trajectory under the **identical externally supplied control sequence**.

| Obligation | Resolution | Evidence |
|---|---|---|
| An exact abstract update implies equality of next observations within each observation class | Checked | `ExactAbstraction.exact_factor_iff`, forward direction |
| Compatible observation classes yield an abstract update | Checked; uses classical choice of representatives | `ExactAbstraction.exact_factor_iff`, reverse direction |
| The abstract update is unique on all observations | Checked; uses surjectivity | `ExactAbstraction.exact_factor_unique` |
| One-step agreement preserves controlled trajectories | Checked by induction | `trajectory_preservation`, `compatible_gives_trajectories` |
| The chosen rule-hiding projection can fail the criterion | Checked two-bit witness | `TwoBit.projection_collision`, `TwoBit.no_state_only_update` |
| The example's full dynamics really oscillate | Checked exact eventual period two | `TwoBit.period_two_after_first`, `TwoBit.exact_period_two_after_first` |

**Evidence:** [ExactAbstraction.lean](exact-abstraction/ExactAbstraction.lean), [formal scope](exact-abstraction/README.md), and [public verification receipt](exact-abstraction/PUBLIC-VERIFICATION.json). The receipt records eight selected endpoints for this module. The criterion is established quotient/congruence mathematics; no novelty is claimed.

**Residual gap:** this does not show that every process/result projection fails, that natural time follows from self-reference, or that a biological representation is adequate. It provides neither a computable construction for arbitrary types nor an entropy/information-loss measure. The fixed joint-state update can contain a rule variable; it does not formalize unrestricted changes of language or semantics. Feedback controls that depend on hidden state require their own preservation contract.

**Next bounded step:** for each proposed application, write its concrete state, observation, permitted action, and preserved quantity. Then either establish compatibility or give two admissible states with equal observations and unequal required outputs. Q09 is a completed application of that pattern.

## Q09 — changing membership is not the whole state of a splitting player

**Source:** §6.4.3, PDF p.22 asks for mathematical understanding of games in which decisions merge or split the decision makers. The paper discusses changing payoffs and individuality. Our target isolates one structural operation; it does not define or solve the whole game.

### Precise specification

There are four persistent sites. A player is a binary merge-history tree; a state is an ordered forest in which every site appears exactly once. The observation is the **unordered set of unordered current member sets**. A split of the designated composite restores its two immediate predecessor trees.

Two legal histories start with the four separate sites and retain site 3 as a spectator:

```text
left:  merge(0,1), then merge({0,1},2)
right: merge(1,2), then merge(0,{1,2})

present partition in both: {{0,1,2},{3}}
left after split:          {{0,1},{2},{3}}
right after split:         {{0},{1,2},{3}}
```

The designated first composite has the same site support in both witnesses. Thus the counterexample holds the chosen current group fixed. It does not depend on selecting different groups after forgetting their order.

**Conclusion:** there is no deterministic function of the current membership partition that reproduces this predecessor-restoring split for all legal states where the designated split is admissible. The weaker totalized exact-update contract also fails.

| Obligation | Resolution | Evidence |
|---|---|---|
| Splitting preserves the legal state invariant | Checked | `MergeHistoryProjection.split_preserves_legal` |
| Both histories are produced by two adjacent merges from the same initial forest | Checked; adjacency here is list adjacency | `adjacent_merge_histories`, `legal_histories` |
| The selected split is admissible in both states and a spectator remains | Checked | `admissible_splits_with_spectator` |
| Present partitions agree despite different hidden predecessors | Checked unordered equality | `same_current_partition` |
| The same chosen group's next partitions differ | Checked | `distinct_restored_partitions` |
| No exact reduced deterministic update exists | Checked by the imported Q04 criterion | `no_exact_partition_model` |
| The obstruction persists when correctness is required only for admissible splits | Checked directly from the two witnesses | `no_partition_only_admissible_split` |
| Pinned implementation operators reproduce the collision | Executed operator test with explicit mocks; separate evidence from Lean | [operator receipt](independent-ipdm-operator-test.json) |

**Evidence:** [MergeHistoryProjection.lean](exact-abstraction/MergeHistoryProjection.lean), [implementation correspondence and limits](exact-abstraction/MERGE-HISTORY.md), and [public verification receipt](exact-abstraction/PUBLIC-VERIFICATION.json). The source contains an actual `import ExactAbstraction` and applies `ExactAbstraction.exact_factor_iff`. Its eight selected endpoints bring the two-module receipt to sixteen; these are declaration counts, not sixteen discoveries.

The implementation test pins [IPDm commit eca9b122480b8c654081d6a844176417aefbbcae](https://github.com/lksshw/IPDm/tree/eca9b122480b8c654081d6a844176417aefbbcae). It executes the relevant original functions with mocked constructors and scalar NumPy helpers. Board adjacency, equal active agent IDs, and the tested metadata belong to that experiment. They are not properties proved by the four-site Lean model.

**Residual gap:** no complete implementation refinement, policy scheduler, probability of reaching the histories, equilibrium theorem, payoff-preserving abstraction, or paper-to-code version equivalence has been proved. The example does not imply non-Markov behavior for every distribution, or rule out a stochastic reduced model after a conditional distribution over histories is supplied. Fixed persistent sites are not automatically biological organisms, cells, or species.

**Next bounded step:** choose the precise future operation that a reduced state must predict, then retain the information needed for that contract. Immediate predecessors suffice to describe one split's output; their recursive histories may be needed for repeated splits. Proving sufficiency or minimality of a smaller memory representation would be a new explicit obligation. A game-theoretic extension also needs controllers, payoffs, and a solution concept.

## Q12 — an unseen branch can be rare instead of impossible

**Source:** §7, PDF p.24 asks how to calibrate evolutionary models whose possible trajectories greatly outnumber observed histories. Our target isolates finite evidence about one fully observed branch.

### Precise specification

Assume $`n\in\mathbb N`$ independent binary trials. Under $`M_0`$ the branch never occurs. Under $`M_e`$ it occurs independently with known probability $`0<e<1`$. Decision rules may randomize. Let $`\alpha`$ and $`\beta`$ be their error probabilities under the two models, and set $`q=(1-e)^n`$.

```math
\min_{\delta}(\alpha_\delta+\beta_\delta)=q,
\qquad
\min_{\delta}\max(\alpha_\delta,\beta_\delta)=\frac{q}{1+q}.
```

These are separate optimization criteria. Their optimal rules may differ.

| Obligation | Resolution | Evidence |
|---|---|---|
| Compute the all-zero sample probability | Written: $`q=(1-e)^n`$ | [derivation](CALIBRATION-BOUND.md) |
| Prove lower bounds for every randomized decision rule | Written: if $`a`$ is its chance of selecting $`M_e`$ after all zeros, then $`\alpha=a`$ and $`\beta\ge q(1-a)`$ | Same derivation |
| Exhibit sharp rules for each optimization criterion | Written and rationally computed in finite instances | Same derivation; [demo](calibration_demo.py) |
| Check the empty-sample boundary | Covered: $`n=0`$ gives sum 1 and minimax error $`1/2`$ | Derivation and recorded finite cases |
| Check implementation arithmetic and small deterministic decision spaces | PASS: 15 cases, 834 deterministic rules | [results](calibration-results.json) |
| Translate the general theorem to Lean | **Open**; no probability proof has been created for this target | No Lean endpoint claimed |
| Connect a realistic evolutionary calibration model to these assumptions | **Open** | Requires a specified observation and sampling model |

**What is solved:** the restricted two-model testing problem has sharp proved-on-paper bounds and an independent mathematical review. The finite program checks are supporting examples, not a proof of all real probabilities and sample sizes.

**Residual gap:** the balanced minimax rule needs the known probability to compute $`q`$. The lower bound still constrains any rule for each fixed positive $`e`$. For a fixed finite sample size, allowing arbitrarily small positive alternatives prevents a uniform worst-error guarantee below $`1/2`$. A known positive lower bound on branch probability can support a specified statistical error level; it does not make non-observation certain proof of impossibility.

For each fixed positive $`e`$, error can approach zero as sample size grows. This is **finite-sample uncertainty**, distinct from different hidden mechanisms giving exactly the same complete observed law. General path-dependent evolution, dependent observations, measurement error, interventions, and counterfactual extrapolation need further models. The original calibration question remains open.

**Next bounded step:** if formal certification of this exact result is prioritized, formalize the finite sample space and randomized decision function, prove the shared all-zero contribution, and supply both attaining rules. Keep structural non-identifiability and biological applicability as separate contracts.

## The other nine questions: what is missing before a theorem can close them

| ID and source locator | Present status | Smallest useful next specification | Completion evidence required |
|---|---|---|---|
| Q01, §2.2 p.5: time and life | Needs definitions and empirical criteria | Distinguish physical time, internal temporal representation, and a measurable biological claim | A selected model plus evidence discriminating its biological interpretation |
| Q02, §3.3 pp.8–9: efficient non-iterative exploration | Needs computation/resource model | Define inputs, success probability, cost, and state-preparation cost | A theorem or counterexample within that complete resource model |
| Q03, §4.2 pp.10–11: self-reference and natural time | Needs semantic and physical definitions | Distinguish a static description, its execution, and physical temporal claims | A precise implication or countermodel; oscillation alone does not settle necessity of time |
| Q05, §6 pp.15–16: interacting rule-changing systems | Needs model and correspondence contract | Specify state, rule syntax, interpreter, environmental inputs, and allowed updates | Semantics and a proved correspondence to a chosen source model |
| Q06, §6.2.3 p.20 and §7 p.24: changing modeling languages | Needs admissible metamodel changes | Specify language transformations, interpretation, and retained invariants | A result under explicit interpreter assumptions; storing rule data alone does not suffice |
| Q07, §6.3 p.21: outgrowing a model or metric | Needs adequacy criterion | Specify observables and a falsifiable adequacy test | An inadequacy witness or preservation theorem for those observables |
| Q08, §6.4.1 p.21: relational self-production and biology | Needs mechanism and empirical correspondence | Select one relational construction and a plausible measurable mechanism | Formal correspondence plus evidence; internal consistency alone is insufficient |
| Q10, §6.4.4 pp.22–23: solution concepts in rule-changing games | Needs exact missing property | Identify the cited domain/powerdomain construction and the failed solution-concept condition | A verified repair or counterexample under the source's actual assumptions |
| Q11, §7 pp.23–24: representation and autonomy | Needs a discriminating formal/operational claim | State which implication or observation would distinguish the two positions | Evidence for that selected claim; no general philosophical resolution is promised |

These are active definitions/evidence gaps, not assertions that the questions are unprovable. No Lean file containing `sorry` or a new assumed theorem has been created to stand in for any of them.

## Connections to existing projects

| Connection class | Actual connection | What transfers | What remains to prove |
|---|---|---|---|
| **Formal import** | `MergeHistoryProjection` imports `ExactAbstraction` and invokes `exact_factor_iff` | The checked general criterion is used inside the checked instance | Broader IPDm/game correspondence remains separate |
| **Shared proof method** | [WongTimedHistory](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/414e79a02ac940da8cd89d58211c5a1fba760233/real/WongTimedHistory.lean) compares histories with equal contracted observations but differing hidden event times and lineage counts | Equal observed input plus incompatible required outputs refutes a universally exact decoder | No import of `ExactAbstraction` is asserted; graph contraction and dynamics abstraction are different specifications |
| **Shared proof method** | [FiniteGenomeIdentifiability](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/414e79a02ac940da8cd89d58211c5a1fba760233/real/FiniteGenomeIdentifiability.lean) uses opposite topology-compatible completions of one finite gARG | Same finite input, incompatible target truth values, hence no universally correct verdict over that completion class | This input is an interval ancestry graph, not a DNA dataset; no genome-owner map or biological species classifier follows |
| **Related statistical issue, different proof** | Q12 uses overlapping finite-sample outcomes under different probability laws | It explains why seeing one finite record does not eliminate every alternative | It is not the equal-full-law or exact-observation collision proved in the other examples |
| **Biological analogy requiring a bridge** | Merging players, cell collectives, ancestral populations, and cognitive systems all raise questions about state and individuality | They motivate candidate definitions and observations | A common vocabulary gives no theorem that these objects share a biological mechanism or a universal minimal-systems theory |

The useful shared question is concrete: **what information must remain available to determine the particular behavior or property we want to preserve?** Its answer depends on the selected state, observation, action, and target. It is not yet a universal measure of the user's “abstraction fee.”

## Completion rule for future work

1. Preserve the author's question and locator.
2. Select one explicit theorem, counterexample, algorithm, or empirical claim with its assumptions.
3. List the obligations and connect each completed one to the exact proof or evidence.
4. Record the precise subproblem as solved only after those obligations are met.
5. Keep the broader author question open until a justified bridge covers its remaining scope.

At this checkpoint, source hashes and receipt content were inspected without rebuilding Lean. The existing receipt records Lean 4.33.1, two clean compiler exits, sixteen selected endpoints, no `sorryAx`, and only its stated standard-axiom allowlist. Hosted publication status belongs to the exact commit's checks and is not inferred from this local proof map.
