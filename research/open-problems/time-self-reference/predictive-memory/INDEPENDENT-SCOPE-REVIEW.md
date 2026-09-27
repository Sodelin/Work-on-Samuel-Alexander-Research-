# Independent scope review: predictive memory

2026-09-27. **Preimplementation mathematical and source-correspondence review.**
Baseline designated by the coordinator: `01db8c4`. This review reads the published
paper, existing ledger, controlled-abstraction bridge, and selected model
declarations. It does not run Lean, certify the new implementation, refresh old
compiler receipts, fit data, or restart an empirical track.

**Recommendation.** Prioritize the universal predictive quotient, its minimality
property, and the arbitrary-finite-history bridge. Add a finite-horizon
stabilization certificate and a delayed-distinguishability counterexample. This
turns the existing obstruction into a general specification of a sufficient
repair. It is a substantive continuation of the selected Q04 problem and supplies
a tool for Q09; it does not close either author question. The mathematics belongs
to established automata, quotient, and coalgebra theory. The contribution here is
verified reuse with explicit intervention and source-correspondence boundaries.

**Source test.** In the published paper, section 4.2, p.11, asks whether process
and result can always be separated, in a discussion that includes proof,
mathematics, and science. Exact deterministic state reduction is one selected
interpretation of that question. It does not establish that projection as a
function is impossible, that mathematical truth requires physical time, or that
self-reference universally requires a temporal model. Section 5.2, p.13, asks
about interpreting memory through bodily and organizational change. Section 7,
p.23, discusses retained path-dependent variables, their use in selecting
futures, and their update through experience or evolution. A predictive quotient
addresses what an external predictor must distinguish; a theorem about an
organism using those variables to pursue goals requires an additional controller
and biological correspondence. See [the published paper](https://doi.org/10.1098/rsos.261059),
and the supplied `paper.pages.md`, lines 647-657, 748-768, and 1383-1390.

The baseline [ledger](../problem-ledger.json) distinguishes two checked selected
subproblems, one written selected subproblem, and zero fully solved author
questions. Those are recorded evidence statuses, not fresh verification by this
review. The [bridge](../controlled-abstraction-bridge/BRIDGE.md), lines 63-129,
already gives all-length written parity reasoning and the coarsest four-state
refinement for its stipulated actions. Its finite enumerations do not replace
those universal statements. Q12's written finite-sample result has exact
assumptions and a remaining Lean obligation; strengthening Q04 should not silently
change Q12's status.

**Exact contract and proof obligations.** Fix arbitrary types `A`, `X`, `O`, a
total deterministic transition `T : A -> X -> X`, and `p : X -> O`. Define
`run [] x = x` and `run (a :: w) x = run w (T a x)`. Define

```text
B(x)(w) = p(run w x)
x ~ y   iff   for every finite action word w, B(x)(w) = B(y)(w).
```

The empty word is essential: it makes `~` refine equality of current output.
Prefixing by an action makes `~` transition-compatible. Thus the quotient has
well-defined output `[x] -> p(x)` and update `[x] -> [T a x]`. Equivalently,
use the image of `B` in `(List A -> O)` and the derivative
`D_a(b)(w) = b(a :: w)`; this supplies a concrete semantic description without
asserting an executable finite construction for arbitrary types.

An exact competing representation consists of an onto `r : X -> R`, decoder
`d : R -> O`, and transitions `G : A -> R -> R` satisfying

```text
p = d ∘ r
r(T a x) = G a (r x).
```

Induction on words shows `r x = r y -> x ~ y`. There is therefore a unique
**surjective** factor `H : R -> X/~` with `H(r x) = [x]`; it also preserves the
declared output and transitions. If `r` is not onto, the statement must use its
image. Unreachable extra elements of `R` invalidate unrestricted uniqueness.
This proves coarseness in the information order, not merely a cardinality
comparison. It also proves that any family of pairwise distinguishable states
must have pairwise distinct `r` values. A family within one visible-output fibre
gives a lower bound on distinctions that the extra retained state must carry.
No Shannon entropy, physical storage cost, or causal memory mechanism follows
without additional definitions and assumptions.

Useful acceptance cases are an empty action alphabet, a nonsurjective competing
map with unused target values, distinguishability at the empty word, and a
restricted transition-closed reachable domain. A global all-state theorem does
not establish necessity on a smaller reachable domain unless its witnesses
belong to that domain. Partial actions need an enabledness-preserving contract
or an explicitly observable failure outcome; arbitrary totalization can create
spurious distinguishing words.

**Stronger results that remain tractable.**

- Mechanize the bridge for every finite binary history, using parity's append
  equations and the common four-state update. The two short tests, the empty word
  and `probe`, recover `(visible, parity)`; they prove coarseness once its update
  equations are proved. Unbounded history length does not imply unbounded
  prediction-relevant memory. A fixed recent-history window can nevertheless
  fail: an earlier parity toggle can remain relevant after arbitrarily many
  zero-appends.
- Define `E_k` as agreement after every word of length **at most** `k`.
  A global equality `E_k = E_(k+1)` makes `E_k` transition-compatible and therefore
  equal to `~`. This is an all-horizon certificate even for infinite `X`.
  Agreement for finitely many sampled states or words is insufficient.
  If `X` has `n` states and `p(X)` has `m` values, successive strict partition
  refinements give some stabilization index at most `n-m`; this is a written
  consequence until separately mechanized. A finite executable checker also
  needs an enumerable finite action set and decidable observations/transitions.
- A delayed witness can use one `wait` action, states `0,...,k+1` and a sink,
  countdown dynamics, output one only at state zero, and permanently zero sink
  output. State `k+1` and the sink agree through `k` steps and differ at `k+1`.
  Consequently no horizon chosen independently of a state bound certifies every
  finite model. This is a proposed mathematical counterexample, not a biological
  delay mechanism or a claim that an implementation has checked it.
- Increasing the allowed intervention set can only refine behavioral
  equivalence. There is a canonical quotient map from the richer predictive
  state to the poorer one. The bridge's addition of `probe` makes this concrete:
  a previously dispensable bit becomes necessary. This directly answers which
  intervention exposes a discarded distinction in the stipulated model.

The most valuable next result after these is a preserved closed control loop:
specify which retained variables drive action selection and prove that the
controller factors through the representation. Same externally supplied actions
do not automatically cover hidden-state controllers. The source's claim about
variables selecting futures needs this extra step. Unknown dynamics, changing
action meanings, and changing state languages remain separate identification or
semantic problems even when an enlarged fixed state can encode particular rules.

**Biological inference must separate retention, prediction, and mechanism.**
Under the declared model, two states with the same `p` and different probe
responses require a distinction somewhere in the sufficient state. That
distinction may be a permanent cell type, an environmental variable, elapsed
time, or a within-cell change. The quotient alone cannot decide which.

The existing internal checkpoint
`cellular-audit/stentor-stable-type-counterexample.md`, lines 21-39, gives an
exact example with a permanent type and type-specific timed response
probabilities. Two histories with the same count and current output predict the
next response with probabilities `7/10` and `3/10`; no prior response changes
the cell's type or future response law. Order information can identify a stable
type. Lines 7-17 distinguish this from the narrower conditional-iid
constant-propensity null, where count plus current response really is
sufficient. The checkpoint is a synthetic rational construction, not a fitted
Stentor mechanism; this review does not rerun its arithmetic receipt.

There is an additional selection trap even when exposure history is randomized.
Let independently fair bits `H` and `Theta` denote assigned history and stable
type, let current visible output be `V = H xor Theta`, and let future outcome be
`Y = Theta`. Changing `H` has no causal effect on `Y`. Nevertheless, among cases
with `V=0`, `Y=H` exactly. Every relevant conditioning event has positive
probability. Thus randomization followed by matching on a history-affected
visible state is not by itself evidence of within-cell memory. This is an
explicit mathematical counterexample proposed in this review, not a data fit or
a mechanistic biological assertion.

A discriminating empirical design must specify the history intervention,
probe, cell identity, measurement times, target outcome, and competing nulls.
Within-cell repeated measurements or randomized exposure sequences can reduce
stable-type confounding, but time trends, selection, censoring, and residual
external exposure still need explicit treatment. To test a specified stable-type
null, a useful exact hypothesis is

```text
Law(Y | do(history=h), do(probe=a), type=theta, context=c)
  = K(theta,c,a)       for every admitted history h.
```

If assigned histories are independent of type and context under a common
sampling scheme, this null implies equal marginal probe laws across histories.
A reproducible intervention effect would reject this null or one of its design
assumptions. It would not identify a storage substrate. Restricting to equal
post-history visible states needs an additional identification argument, as the
counterexample shows. To support a mechanism, independently measure a candidate
retained variable, intervene on it, and test the predicted loss and restoration
of the response difference while addressing effects on exposure and general
responsiveness. Specify these as remaining experimental gates, not as findings.

The public account should consistently distinguish: **mathematical example**
(stipulated transitions, proved consequences), **fitted prediction** (a declared
statistical model evaluated on held-out observations), and **experimentally
supported mechanism** (intervention evidence for a biological causal pathway).
Success at one level does not promote a claim automatically to the next.

**Wong and Alexander: existing maps and missing transport.** The repository is
not devoid of proved bridges. Read-only inspection finds the following explicit
declarations; this review has not refreshed their compilation evidence.

| Existing declaration | What its statement supports | What it does not transport |
|---|---|---|
| `WongAlexander.extracted_sample_path_iff` and `extracted_contracted_sample_path_iff`, `real/WongAlexander.lean`, lines 51-72 | Fixed-location ancestry paths into retained samples survive the specified restriction and contraction. | Controlled updates, intervention semantics, rewards, or a full stochastic history law. |
| `WongAlexander.actual_garg_opposite_infinite_completions`, same file, lines 138 onward | Exact finite graph embedding into two infinite completions with opposite selected species properties. | A biological genome-owner correspondence or a unique inferred future population. |
| `WongTimedHistory.observation_independent`, `lineage_counts_differ`, and `no_exact_lineage_decoder`, `real/WongTimedHistory.lean`, lines 216-269 | A validated contracted observation loses a particular timed-history query. | An intervention dynamics on histories, or a probability that either constructed history occurs. |

A **static** fibre/nondecodability lemma can genuinely be instantiated by the
Wong timed-history definitions: the two observation-equal witnesses have
different lineage counts at the named time. That is a typed mathematical
connection, not a cellular-memory mechanism. To claim the new **controlled**
theorem applies, define concrete state `X`, action interpretation, transition,
observation, preserved outputs, and a map `q`, then prove
`q(T_a x)=G_a(q x)` for every admitted state/action and preserve initial or
reachable states. Record whether event time, intervals, sample membership, and
action admissibility are retained. A static graph path equivalence does not
prove this commuting equation.

For a stochastic Wong model, replace the deterministic equation with a
measurable kernel pushforward contract, `q_* K_a(x) = Kbar_a(q x)`, and preserve
the initial law. Include holding times and event marks if the target concerns
timed or marked histories. A count chain already defined to be Markov does not
by itself prove that a richer graph-generating process projects to that chain.
Reward or policy claims require reward and controller preservation as well.

Alexander's population graphs require an explicit temporal/action semantics
before a controlled theorem applies. Passing from genomic nodes to organisms
also requires a specified owner map and the relevant edge/path and birth-order
properties, with reflection when an equivalence is claimed. A finite catalog
does not satisfy an infinite-population hypothesis; the explicit opposite
completion theorem already obstructs inference of the selected asymptotic
species property from that catalog alone. Retaining an analogy is appropriate
until these exact obligations are proved. Do not describe the selected Q04
theorem as a theorem asserted by the Royal Society authors.

**Primary prior work inspected.**

- [Rutten, *Universal coalgebra: a theory of systems*](https://ir.cwi.nl/pub/48):
  Moore machines in section 3, published pp.21-22; quotient factorization in
  Theorems 7.1-7.4, pp.38-39; simple quotients in Proposition 8.2, pp.40-41;
  behavioral equivalence in Theorem 9.3, p.42. The relevant passages were read
  through [this full-paper mirror](https://pages.jh.edu/rrynasi1/NewFoundations4Math/Literature/Coalgebras/Rutten2000UniversalCoalgebra-ATheoryOfSystems.pdf).
  They establish direct prior art for the proposed semantic quotient; this
  review does not claim to have reverified the entire general theory.
- [Givan, Dean, and Greig, *Equivalence notions and model minimization in Markov decision processes*](https://cs.brown.edu/people/tdean/publications/archive/GivanetalAIJ-03.pdf):
  section 3.2/Theorem 2 gives the finite-machine quotient; section 4 describes
  stabilization by refinement; Theorem 7 adds optimal-policy transfer under
  stochastic bisimulation including reward preservation. These are stronger
  assumptions than common output alone.
- [Littman, Sutton, and Singh, *Predictive Representations of State*](https://proceedings.neurips.cc/paper/2001/file/1e4d36177d71bbb3558e43af9577d70e-Paper.pdf):
  section 1 uses action-observation tests; Theorem 1 relates finite POMDPs to
  linear predictive representations. This is a directly relevant stochastic
  continuation, not proof that the current deterministic construction learns
  its state from finite biological data.
- [Shalizi and Crutchfield, *Computational Mechanics: Pattern and Prediction, Structure and Simplicity*](https://arxiv.org/abs/cond-mat/9907176):
  predictive-state minimality and uniqueness are prior art. The inspected
  version's section III assumes discrete-valued, discrete-time stationary
  stochastic processes. Its observational construction must not silently be
  treated as a biological intervention theorem.

**Suggested newcomer wording, conditional on actual verification.** “The paper
asks how living systems can remember, anticipate, and change themselves while
remaining coherent. We have made one part precise: if two situations look the
same now but can respond differently to an allowed intervention, an exact
predictor must retain a distinction between them. The new construction identifies
the smallest sufficient predictive description for a specified deterministic
model. It tells us what a useful experiment must distinguish, but does not yet
tell us which molecular mechanism stores that distinction. The paper's full
questions remain open.” Link this paragraph directly to the proof receipt,
worked history bridge, empirical limits, and ledger rather than making a reader
search the repository.

---

**Postimplementation statement review, 2026-09-27.** This appendix is a separate
read-only review of the implemented contracts and proofs. It does not change the
preimplementation record above. The reviewer ran no Lean processes and edited
only this review file. The coordinator supplied an initial successful pass; the
inspected `verification/PROOF-RECEIPT.json` records 47 selected new theorem axiom
reports at `2026-09-27T03:20:59.062382+00:00`, with no unexpected axioms. Further
owner edits were in progress during this review. A read-only hash comparison
found that `PredictiveState`, `ControlledMemory`, and `HistoryObservation` had
already changed after that receipt; `AncestryObservation` still matched it.
`WongPredictiveBridge` and the later additions therefore require the final
receipt for their actual source bytes. Statement acceptance here is not a new
compilation claim.

**Outcome: no mathematical blocker found in the inspected final contracts.**
Several boundaries and one useful strengthening were identified during review;
the owner revised the completion theorem and added explicit feedback and
reachability results. The observations below distinguish what the statements
prove from tempting extensions.

- `PredictiveState.coarsest_exact` states the intended universal property. It
  requires an onto encoding `c`, output decoding, and actionwise update
  commutation. Its conclusion includes a surjective factor onto the quotient,
  commutation of that factor with every action, preservation of output, and
  uniqueness among all maps with the required factorization. The proof uses
  surjectivity exactly where arbitrary abstract codes must be represented. It
  does not assume the result or quietly restrict to a singleton model. The
  quotient output and transition are independently well-defined using empty
  words and prefixed words. In this generic theorem, “attained codes” is more
  precise than “reachable codes”: no initial state or reachability predicate is
  present in its hypotheses.
- `depth_iff_words` correctly characterizes words of length at most `n`, including
  length zero. `stabilization_complete` assumes the global implication
  `DepthEq n x y -> DepthEq (n+1) x y` for every pair. Its induction on action
  words then proves all-horizon agreement. This is a sufficient certificate, not
  a theorem that a supplied model stabilizes, a finite-state termination bound,
  or an implemented partition-refinement algorithm. The `n-m` bound proposed
  earlier remains written unless a separate declaration is added and checked.
- `ControlledMemory.history_commutes`, `cross_model_all_words`, and
  `cross_model_all_times` quantify over arbitrary finite initial records and
  arbitrary horizons. They do not rely on finite enumerations. The two
  `future_iff` results show that current output plus parity/memory is precisely
  the behavioral distinction for the four stipulated actions. `at_least_four`
  injects all four distinct Boolean pairs into any exact representation; the
  lower bound is genuine and unused target codes do not evade it. The revised
  comment says “attained,” and `all_summaries_reachable` separately supplies
  action words attaining all four summaries from the displayed initialization.
- The revised `reachable_probe_witness` compares `reset; wait` with
  `reset; prime`, followed by the same probe. The histories now have equal
  lengths, the same initial cell and visible result, and unequal probed outputs.
  This avoids accidentally using different clock times to motivate the later
  fixed-type null. It remains a stipulated Boolean example.
- `no_finite_suffix_decoder` uses an all-zero history and a history with one
  earlier true bit followed by the same zero suffix. The equal-suffix witness
  includes `n=0`. This proves that a fixed suffix cannot replace the retained
  parity bit; it does not prove an unbounded memory-capacity requirement.
- The newly added `feedback_trajectories` resolves the initial one-step-only
  limitation of `feedback_commutes`. It quantifies over all times and explicitly
  assumes that the concrete controller's chosen action equals a policy of the
  retained state. This is the right extra hypothesis. It does not claim that
  every hidden-state controller satisfies it or establish a biological goal,
  reward, learning rule, or optimum.

**Interpretation of history nulls.**
`HistoryObservation.stable_type_matched_history_null` fixes the same complete
initial pair `(clock,type)`, lets actions advance only the clock, and compares
equal-length words. The output is an arbitrary deterministic function of that
pair. Its conclusion is correct for this specified counterfactual null. It is
not a rejection threshold for stochastic observations, nor does one unequal
pair of noisy experimental responses reject all permanent-type models. A
statistical null needs response laws, sampling and an uncertainty calculation.

`arbitrary_delayed_distinction` uses the actual infinite state type `Option Nat`.
It proves agreement through each chosen finite horizon and a later mismatch in
that fixed countdown/silent model. This is sound and nonvacuous. The implemented
statement does not itself assert a finite-state cardinality bound; the finite
countdown truncations proposed earlier are a further written specialization.

The newly read `selection_no_history_effect` and
`selected_history_perfectly_predicts` express the Boolean collider example's
structural identities correctly. They are deterministic implications. The
independently uniform probability table and its positive conditioning masses
must be supported by the separate evidence the coordinator intends to provide;
these two statements alone contain no probability model. Their final compiler
status must also come from a receipt that includes the additions.

**Interpretation of ancestry processing.** `restriction_all_words` is an actual
instance of `run_commutes` using the imported `AncestralRestriction.Restrict`.
It states equality between two successive destructive-processing pipelines:
first compress to original samples `S`, then perform the same declared
restrictions, or perform them on the source relation and compress afterwards.
Every action's selected samples are a subset of the original `S`. This does not
mean a discarded edge can be restored by a later request. For example, after a
restriction to the empty sample set, requesting `S` again leaves an empty
relation on both sides of the equality. Nor does this theorem prove that the
chosen compression is minimal for every graph query.

`no_universal_sample_expansion` has an explicit collision. At sample `{2}`,
`SplitLocus` and `VisibleTail` have equal compressed relations. Adding sample
`1` exposes edge `0 -> 1` at index `false` in only the first relation. The
imported `splitLocus_time` and `visibleTail_time` establish that their edges
respect increasing natural-number time. These are indexed relational examples
with finitely many non-isolated vertices; the declaration does not itself package
them as finite interval-gARG records. Its formal no-decoder quantifier is over
all indexed relations. The displayed witnesses explain why the obstruction is
not an artefact of cycles or inconsistent time order.

`WongPredictiveBridge.actual_garg_restriction_all_words` uses the actual
`WongGARG.GARG` input and `WongAlexander.extracted_edge_iff_restrict` to identify
its sample extraction with the generic compression. The controlled state space
is then the binary relation at one fixed genomic location. Its actions process
that relation; they do not edit interval-record data structures, simulate a
marked ARG generator, or intervene on organisms. Within that stated scope, this
is a proved mapping once its final compilation is confirmed, not a mere
analogy. It does not transfer the quotient's minimality theorem to a new claim
about all Wong representations.

**Completion-specific strengthening.** The first draft of
`WongPredictiveBridge.no_global_iap_decoder` ruled out a decoder over all
real-dated populations, while its prose mentioned completions of the supplied
finite graph. The reviewer requested the completion restriction explicitly.
The subsequently inspected version includes all of the following premises on a
candidate population `E`:

```text
RealDatedBiosphere E
FiniteSupport (Root E)
WeaklyConnected E Whole
finiteView code E = (G.Topology, fun a b => Reach G.Topology a b).
```

This is the stronger and source-appropriate no-decoder statement. The imported
`actual_garg_opposite_infinite_completions` supplies two actual witnesses
satisfying these premises. Their views preserve both old edges and old ancestry
paths exactly, while one satisfies global IAP and the other fails it. Inspection
of `SpeciesBridge.MaximalSpecieslike` and `Specieslike` confirms that the proof's
`maximalE.1.2.1` extracts exactly the needed IAP premise. Thus the contradiction
does not rely on an empty admissible class or on arbitrary future graphs that
violate the known finite view.

The decoder has codomain `Prop` and is not required to be computable. The result
therefore concerns insufficiency of this observation even for an unrestricted
mathematical decoder, not a halting-problem style undecidability theorem. The
finite view omits biological ownership and actual future evidence; the result
does not deny that additional assumptions or data can discriminate particular
populations. Its final compilation and axiom audit were still the coordinator's
separate responsibility at the end of this statement review.

## Final public-document scope review

This bounded pass inspected `TIME-AND-MEMORY.md` and this packet's `AUDIT.md`,
`RESULTS.md`, and `BIOLOGY.md`. It did not run Lean or the example checker, and
does not independently certify the coordinator's reported build. The
coordinator reports that all five new modules and the development audit pass;
the final fresh replay remains a separate publication receipt.

One substantive wording defect was found and corrected by the coordinator:
the finite checker cannot find separating words for every ordered pair, since
equivalent pairs have none. The revised `RESULTS.md` correctly says that all 64
pairs are examined, shortest witnesses are found for distinguishable pairs,
and equivalent pairs have no witness. The inspected checker asserts precisely
that equivalence/no-witness correspondence.

The corrected stable-type example in `BIOLOGY.md` also matches the exact
enumeration: the complete observed histories are `000010` and `000100`.
Both contain one positive response and end in zero. Each conditioning event
has probability `5/256`, and the respective predictions for response seven are
`7/10` and `3/10`. The histories contain six responses, not five; the five-entry
tuples in the code are followed by the common sixth response. This is a
positive-support mathematical counterexample with invented probabilities,
not a biological fit.

The primary biological citations were checked directly. Durant et al. (2017),
[results and physiological methods](https://pmc.ncbi.nlm.nih.gov/articles/PMC5443973/),
support the stated combination of altered regenerative outcomes, physiological
measurement and intervention, including the stochastic outcomes and limited
depth of voltage measurement. The
[Stentor reviewed preprint, version 1](https://elifesciences.org/reviewed-preprints/112314v1),
supports the separate account of single-cell stimulation/recovery observations
and latent response-curve fitting. Neither establishes a correspondence with
this packet's Boolean transition system or identifies a minimal biological
state.

A minor provenance correction in `BIOLOGY.md` is also resolved. The coordinator
removed the unlinked prior-fit result and audit claims, leaving the directly
reviewable statement that this continuation ran no biological fit or
experiment. The revised text says explicitly that the invented examples do
not reproduce or validate the separate Stentor data-analysis track. The
rational example no longer depends on attribution to an earlier local
counterexample. Both edits were read after they were applied.

After these wording corrections, this final pass found no remaining material
overclaim in the four requested pages. In particular, the pages preserve the
deterministic/total-action contract, the global stabilization premise, the
destructive nature of graph restriction, the fixed-locus scope of the actual
gARG mapping, the finite-view restriction of the IAP obstruction, and the
distinction between predictive adequacy, intervention evidence and biological
mechanism. They retain all authors' full questions as open.
