# Exact predictive state, memory, and the intervention boundary

Continuation of the [problem ledger](../problem-ledger.json) and
[controlled-abstraction bridge](../controlled-abstraction-bridge/BRIDGE.md).
Status: **PASS**, fresh committed-source replay. All 35 project imports compiled;
56 new theorem declarations and 16 historical selected endpoints passed the
transitive axiom audit. The source-hashed receipt identifies the exact inputs.
These counts include supporting lemmas and do not count discoveries or solved
author questions.

## The general result

Fix arbitrary state, action and output types `X`, `A`, `O`, a deterministic
total transition `T : A → X → X`, and visible output `p : X → O`. A word is a
finite list of interventions in chronological order, including the empty word.
Write `run(T,w,x)` for the result of applying it to `x`. Define

```math
x\sim y\quad\Longleftrightarrow\quad
\forall w\in A^*,\ p(\mathrm{run}(T,w,x))=p(\mathrm{run}(T,w,y)).
```

The quotient `Q = X / ~` has a well-defined observation and a well-defined
controlled transition. Its encoding `q : X → Q` preserves current output and
every action. The empty word is essential: it retains the current observation.

Let a competing representation `c : X → R` be onto, with output decoder `d`
and update `G`, satisfying `d(c(x))=p(x)` and `c(T(a,x))=G(a,c(x))` everywhere.
Then there is a unique `H : R → Q` with `H(c(x))=q(x)`. It is onto, commutes
with every action, and preserves the output. Hence `Q` is no more informative
than any exact output-preserving representation. Replace `R` by the image of
`c` if it contains unattained codes; unrestricted uniqueness would otherwise
be false. This is **coarseness by factorization**, not an entropy theorem.

`PredictiveState.coarsest_exact` proves all these properties together. The
quotient uses existing Lean/Mathlib quotient and function mathematics.
`distinguishing_word` says unequal quotient states admit a finite intervention
word with different outputs. For arbitrary infinite systems this is a
classical existence result, not a computable search or a uniform length bound.
`distinguishable_injective` and `distinguishable_card_le` prove that every
family of pairwise distinguishable states requires at least that many
attained representation values. The lower bound can be applied within a
fixed visible-output class to isolate additional memory distinctions.

## Intervention scope, feedback, and finite verification

`restrict_actions` proves that allowing fewer actions can merge predictive
states. Thus the required state depends on the interventions admitted, not
only on the passive observations collected.

The general trajectory statement compares identical controls. For an actual
state-dependent controller `choose : X → A`,
`feedback_trajectories` additionally assumes `choose(x)=policy(c(x))` and then
preserves the resulting closed-loop trajectory for every time. It does not
infer that an unknown biological controller uses a decoded variable. A
controller with its own memory must have that memory included in the state.

`DepthEq(k)` compares all words of length at most `k`, as proved by
`depth_iff_words`. If, **for every pair of declared states**, equivalence at
depth `k` implies equivalence at depth `k+1`, `stabilization_complete` proves
equivalence at all finite horizons. This is a global fixed-point certificate,
not an inference from sampled agreement. The executable finite-state checker
finds partitions of sizes `2,4,4` for the eight-state example, and `2,2` when
probe is excluded. The checker examines all 64 ordered state pairs, finds
shortest separating words for distinguishable pairs, and reports no witness
for equivalent pairs. These computations supplement the general
Lean proof; the checker itself is not a Lean-verified algorithm.

`HistoryObservation.arbitrary_delayed_distinction` constructs, for every
horizon `n`, a countdown state and a permanently silent state that agree for
every word of length at most `n` but disagree at `n+1`. No uniform finite
experimental horizon works for arbitrary infinite state spaces. The familiar
finite-state partition-count bound is reviewed in the independent note but
has not been mechanized here.

## The formerly written-only history bridge

The model definitions reproduce the old bridge: cell state `(visible,memory,
nuisance)`, history state `(visible,finite Boolean record)`, and summary
`(visible,parity(record))`. Wait appends zero, prime appends one, probe displays
memory, and reset clears it. The cell's nuisance bit toggles on every action.

| Formal result | Exact scope |
|---|---|
| `ControlledMemory.history_commutes` | Parity is sufficient for every finite record, with no length bound. |
| `cross_model_all_words`, `cross_model_all_times` | Both different state spaces implement the same summary for arbitrary inputs and horizons. |
| `probe_refinement_factor` | Mechanizes the old packet's open decoder/factorization obligation for arbitrary types. |
| `cell_future_iff`, `history_future_iff` | The two-bit summary coincides exactly with future-output equivalence. |
| `at_least_four`, `all_summaries_reachable` | At least four attained predictive codes; all four summaries arise from one initialization. |
| `memory_required_at_fixed_visible` | Each visible value still requires two distinct retained codes. |
| `no_finite_suffix_decoder` | No fixed recent-record window determines parity for all records; unbounded lookback and memory capacity are different. |
| `reachable_probe_witness` | Equal-length histories from the same initialization have equal visible outputs and different probe responses. |
| `passive_future_iff` | Without probe, visible output alone is sufficient. |
| `changed_probe_refutes_summary` | A probe that also reads the nuisance bit invalidates the old summary. |

The word “cell” is an interpretation of stipulated Boolean variables. There
is no fitted cellular transition law, learning algorithm, thermodynamic cost,
or mechanism identification in these definitions.

## Proved transfer to ancestry operations

`AncestryObservation.compress(S,R)` is the repository's existing ancestral
restriction: retain edges whose child is ancestral to a sample in `S`.
Actions destructively restrict the current relation to ancestors of any
`A ⊆ S`. Using the existing nested-restriction theorem, `restriction_commutes`
proves that compression to `S` and each action commute. `restriction_all_words`
then invokes the general controlled-run theorem. It equates **two destructive
processing pipelines**; processing `[empty,S]` cannot restore discarded edges.

`WongPredictiveBridge.extracted_is_compress` identifies this operation with
`G.ExtractedAt(x)` in the actual finite interval-gARG structure, via the
existing `WongAlexander.extracted_edge_iff_restrict` mapping.
`actual_garg_restriction_all_words` is therefore an instantiated theorem, not
just an analogy. Its state is a relation at a fixed locus. It is not an update
of interval records or the marked stochastic ARG-generation process.

`no_universal_sample_expansion` uses the existing time-ordered split-locus and
visible-tail graphs. Their sample-2 compressed relations agree, but adding
sample 1 exposes a differing edge. No universal decoder can recover this
enlarged-sample relation from the old compressed relation alone.

For every finite interval gARG, `no_global_iap_decoder` reuses the existing
opposite infinite completions. Its witnesses preserve both the exact old
edges and old ancestry paths; both have real birthdates with finite date
sublevels, finite child sets, finite root sets, and connected whole graphs.
One satisfies global IAP and the other does not. Thus no decoder of that
finite view correctly decides IAP over all such completions, even with the
finite gARG fixed. Here IAP means that every vertex has either finitely many
descendants or only finitely many non-descendants in the declared population.
This is information insufficiency, not computational
undecidability. Genome nodes have not been identified with organisms; a
biological species interpretation and a marked-process projection require
their own maps and hypotheses.

## Prior mathematics and source correspondence

This construction belongs to established behavioral equivalence, Moore-machine
minimization and coalgebra. See [Rutten, sections 3 and 7–9](https://ir.cwi.nl/pub/48)
and [Givan, Dean and Greig, sections 3.2 and 4](https://cs.brown.edu/people/tdean/publications/archive/GivanetalAIJ-03.pdf).
Predictive stochastic states have related but different assumptions; see
[Shalizi and Crutchfield](https://arxiv.org/abs/cond-mat/9907176) and
[Littman, Sutton and Singh](https://proceedings.neurips.cc/paper/2001/file/1e4d36177d71bbb3558e43af9577d70e-Paper.pdf).
No novelty claim is made for the quotient or the elementary counterexamples.

The primary Royal Society source is the published 29-page PDF, SHA256
`8b3940d8ac53c7145584c38c1a95a27c87f9c8173323112865c5439862bf43ce`.
Q04 (§4.2, p.11) motivates the projection question; §5.2 (p.13) motivates memory
through remodeling; §7 (p.23) explicitly discusses path-dependent internal
variables used to select futures. Q07 (§6.3, p.21) motivates adequacy tests.
Fixed deterministic semantics, known states, total actions and selected outputs
are our abstraction choices. They do not formalize new physical time, organismal
identity, changes of interpretation/language, or complete biological agency.

## Replay

Use the pinned Lean `4.33.1` and the `real/lakefile.lean` Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`. After resolving that existing package's
dependencies and cache, run:

```text
python research/open-problems/time-self-reference/predictive-memory/verify.py --dependency-root real
python research/open-problems/time-self-reference/predictive-memory/check_examples.py
```

On this host, `--dependency-root` points to the already populated original
research checkout's `real` directory and `--lean` selects its pinned compiler.
All project imports are freshly rebuilt from this isolated checkout; only
external package oleans are reused. The final receipt must say
`fresh_project_rebuild: true`. The development switch is for repair iterations.
Every new top-level theorem and the 16 historical selected endpoints get an
axiom report; only `propext`,
`Classical.choice`, and `Quot.sound` are allowed. A separate audit checks source
hashes, exact Git inputs and local reading links, and keeps evidence counts
distinct from discoveries. The dedicated `Predictive memory proofs` workflow
rebuilds this import closure on Linux and preserves its own run receipt; a
committed local PASS does not assert that the hosted run passed.
