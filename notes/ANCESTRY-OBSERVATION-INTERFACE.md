# Ancestry representations, observation, and exact prediction

## Purpose and status

These four modules provide a small checked interface between indexed ancestry,
the package's organism ancestry relation, and information retained by an
observation. They are elementary relation, quotient, and aggregation facts. We
claim a local formalization and a useful explicit interface; we claim no new
general theorem about observation or ancestry.

The long-term motivation is to make the assumptions behind prediction and
classification explicit, including eventual applications in psychology. Such an
application needs its own state variables, measurement model, and evidence.
These lemmas alone do not establish a theory of consciousness, biological
species delimitation, or the validity of a psychological model.

## Checked statements and their assumptions

| Module | Main conclusion | Assumptions that an application must provide |
|---|---|---|
| [AncestryViews](../lean/SamuelAlexanderResearch/AncestryViews.lean) | Fixed-index paths survive forgetting the index; the converse can fail. A common strict clock also survives. | The actual indexed edge relations; a single increasing natural-number clock for the clock statements. |
| [SpeciesAdapter](../lean/SamuelAlexanderResearch/SpeciesAdapter.lean) | The generic nonempty path and erasure definitions agree with the package's existing ancestry and label-forgetting definitions. | The supplied graph on natural-number vertices. No preservation of species predicates is asserted. |
| [HistoryProjection](../lean/SamuelAlexanderResearch/HistoryProjection.lean) | Every genetic-history path maps to equal organism owners or an organism-ancestry path; distinct owners imply strict ancestry. | Each genetic edge must already map to equal owners or a strict organism-ancestry path. |
| [ObservationPrediction](../lean/SamuelAlexanderResearch/ObservationPrediction.lean) | Exact recovery is equivalent to agreement of the target on states with equal observations. Exact next-observation prediction is equivalent to preservation of observational equality by the transition. | A state type, observation map, target, and (for prediction) total deterministic transition. The conditions quantify over all states. |

The observation decoder has type `Observation -> Option Answer`: it is a total
function allowed to return `none` outside the observation image. Correctness
forbids `none` on realizable observations. The converse existence constructions
use classical choice; downstream theorems may inherit those dependencies. These
proofs provide no executable decoder or predictor, measurability guarantee,
statistical estimator, or sample-complexity result.

The explicit two-bit example concerns ambiguity from the **current observation
alone**. Its hidden bit becomes visible after one transition, so observations
at times zero and one recover both original coordinates. It is not an example
of permanent unobservability. A model restricted to reachable or admissible
states should use that state space and prove closure under its transition.

## How the genome representation connects

Wong et al.'s published 2024 paper defines genome ARG edges using inherited
genomic intervals. Nodes can describe genomes at cellular events; edges may
summarize multiple generations. Section “Genome ARGs” and Figure 1 already
explain a genome ARG embedded in a pedigree. This connection is established
prior work. The final version of record was checked for these specific passages:
[journal pp. 2–3](https://www.pure.ed.ac.uk/ws/portalfiles/portal/458588307/iyae100.pdf),
[DOI 10.1093/genetics/iyae100](https://doi.org/10.1093/genetics/iyae100).

Our `owner` map may identify multiple genome nodes with the same organism.
The adapter assumes the compatibility of each genetic edge with the chosen
organism graph. Horizontal genetic transfer need not meet this premise for a
purely reproductive pedigree; no unconditional correspondence is claimed.
The owner assignment itself needs justification: a constant owner map satisfies
the equality alternative trivially. This is an ancestry-preserving map under
the supplied hypothesis, not an injective embedding.
Edges here point from ancestor to descendant, so a source using the reverse
direction must first be translated explicitly.

The interval records are a minimal finite-list interface. They do not enforce
disjoint intervals, genomic coverage, sample resolution, unique-parent
conditions, global acyclicity, or a mutation/inference model. The path projection
lemma does not need these additional conditions, and does not certify them.
It also does not turn a finite ARG record into an infinite population satisfying
Alexander's axioms. Deriving his species or sequence theorems from other work
would require separate translations and hypothesis checks.

`Reach` and `Descendant` mean a nonempty directed path. Arbitrary input relations
can contain cycles; global irreflexivity requires acyclicity or an increasing
clock. The distinct-owner endpoint lemma remains valid without that extra
condition. The adapter equates raw relations; it establishes neither the
population axioms nor species-cluster preservation. In particular, one genome
edge can carry several loci, whereas `BinaryPopulation.UniqueLabels` allows
only one Boolean label per edge.

## Closest established mathematics

| Result in this contribution | Prior framework | Exact relationship and limit |
|---|---|---|
| Recovery iff constancy on observation fibres | Quotient factorization; [Cornell, Universal Mapping Properties, Theorem 1](https://pi.math.cornell.edu/~kassabov/math4330.fall19/cornell-only/Universal.pdf) | Apply the universal property to the equivalence relation “has the same observation.” The quotient identifies with the observation image. `Option` extends the decoder off that image. This teaching source explains the existing theorem, rather than establishing its original priority. |
| Exact deterministic next-observation prediction | Finite Markov-chain lumpability; [Kemeny and Snell, Theorem 6.3.2, p. 124](https://math.pku.edu.cn/teachers/yaoy/Fall2011/Kemeny-Snell_Chapter6.3-4.pdf) | Our deduction: for deterministic finite transitions, the probabilities of entering each observation block are zero or one, so the lumpability criterion becomes our compatibility condition. The indexed original theorem text was inspected; direct PDF retrieval timed out. Our theorem itself allows arbitrary state types. |
| Projected dynamics commute with observation | [Horstmeyer and Atay, Exact Lumpability for Vector Fields, section 2.2](https://arxiv.org/html/1607.01237#S2.SS2) | A continuous-time analogue with smooth-manifold and differential hypotheses. Our code proves a discrete set-theoretic criterion; it does not formalize their results. |
| Distinguishing states using measurements over time | [Hermann and Krener, Nonlinear Controllability and Observability (1977)](https://www.math.ucdavis.edu/~krener/1-25/10.IEEETAC77.pdf) | A single-time collision is weaker than indistinguishability under observation histories or experiments. Controls, rank conditions, and observer construction are absent here. |
| Predictive state representations | [Shalizi and Crutchfield, Computational Mechanics (2001)](https://csc.ucdavis.edu/~cmg/papers/cmppss.pdf) | Their predictive sufficiency and minimality concern distributions over futures. These stronger stochastic results are background, not claims of our deterministic module. |

Path preservation follows by induction and transitivity. Index erasure is a
union of relations; its failure to commute with nonempty transitive closure
has the explicit two-edge witness in the code. The bounded literature review
establishes clear prior frameworks for these interfaces. It neither certifies
priority for an application nor makes a claim that an author overlooked them.

## Verification and integration record

All four modules target the package's pinned Lean 4.33.1. They contain 26
explicitly printed public audit endpoints, with supporting declarations also
checked by the compiler. The standalone sources were checked before adaptation;
the package adaptation changes two imports and one scope comment. The owning
package audit must register the 26 endpoints and import all four modules.
The receipt accompanying the contribution records the exact local build and
source hashes; the repository's global status is governed by its integrated
audit and CI. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted
dependencies, with no project-specific axioms or unfinished proof placeholders.

## Logical argument register


The user requested an explicit record of the logical arguments created during
this work. The entries below group the current theorem declarations by argument.
The Lean files contain the full statements and proof terms, including supporting
steps. These are standard mathematical arguments instantiated and formalized
here; this register makes no claim of first discovery. General applicability and
mathematical novelty are separate questions.

For future contributions, record the assumptions, conclusion, short public proof,
Lean declaration or unchecked status, source/novelty status, and interpretation
limits. An unproved candidate should be labelled as such. An empirical assumption
does not become established merely because its mathematical consequences compile.

### 1. Preserving paths when edges are preserved

If every edge of one relation belongs to another relation, each finite path in
the first is a path in the second. Proof: transfer the first edge, then extend
the transferred path one edge at a time. Erasing an edge's index retains the edge,
so this argument applies to every path following one fixed index.

Declarations: `reach_mono`, `fixed_index_path_survives` (AncestryViews.lean).

### 2. Preserving increasing time

If time strictly increases along each edge, transitivity of the time ordering
makes it increase along every nonempty finite path. Erasing indices retains this
property when all indexed edges obey the same clock. The example's edges also
satisfy increasing time.

Declarations: `reach_time_increases`, `erased_path_time_increases`,
`splitLocus_time` (AncestryViews.lean).

### 3. Erasure can remove information needed for a conclusion

Give edge 0-to-1 one index and edge 1-to-2 a different index. Their union has a
two-step path, while neither individual index has that path. Giving both edges
the same index produces the same union graph but a different answer to the
fixed-index ancestry question. Thus the union graph does not determine that
answer. These are explicit finite counterexamples, not empirical biological data.

Declarations: `erased_two_step_path`, `no_fixed_index_path`,
`erasure_converse_fails`, `erased_histories_agree`, `same_locus_two_step_path`,
`erased_graph_does_not_determine_fixed_index_ancestry` (AncestryViews.lean).

### 4. Connecting definitions to the existing package

The generic nonempty path definition and SpeciesBridge.Descendant describe the
same paths: induction translates each constructor in both directions. Erasure
agrees with the existing ForgetLabels definition. The path implication and its
failed converse therefore apply to the package's actual ancestry relation.

Declarations: `reach_iff_species_descendant`, `erasure_eq_existing_forget`,
`fixed_index_to_species_descendant`, `species_descendant_need_not_have_one_index`
(SpeciesAdapter.lean).

### 5. Projecting genetic histories onto organisms

Assume each genetic edge maps to equality of owners or an organism ancestry
path. Equality and ancestry compose, so induction projects any finite genetic
path. Distinct endpoint owners exclude equality. Indexed edges, their union,
and interval-record edges instantiate the same argument after their respective
edge-compatibility assumptions are supplied. This does not prove those premises
for a complete ARG model or preserve a species predicate automatically.

Declarations: `sameOrDescendant_trans`, `path_projects`,
`path_projects_strict_of_distinct_owners`, `locus_path_projects`,
`erased_path_projects`, `interval_record_path_projects` (HistoryProjection.lean).

### 6. Exact recovery is equivalent to agreement within each observation

Assume an observation function and a target function on the allowed states.
Forward direction: a decoder receives the same input on equal observations,
so its unique correct answer forces the targets to agree. Reverse direction:
if all states giving an observation agree on the target, select a representative
state and return its target; the answer is independent of the selection. Return
none for unrealizable observations. Classical choice supplies the selection;
this existence argument does not establish computability or practical learnability.

Declarations: `recoverable_implies_constant`, `constant_implies_recoverable`,
`recoverable_iff_constant_on_fibres` (ObservationPrediction.lean).

### 7. A conflicting pair obstructs recovery; full state permits it

Two allowed states with equal observations and different targets contradict any
universally correct decoder. A pair of visible/hidden bits witnesses this for
the hidden bit. Observing the full state instead permits returning its target
directly. Failure under one observation function does not prove impossibility
under all possible measurements.

Declarations: `collision_obstructs_recovery`, `hidden_bit_not_recoverable`,
`full_state_recovers_target` (ObservationPrediction.lean).

### 8. Finer observations retain coarse recoverability

If the coarse observation can be computed from the fine one, compose that
computation with a coarse decoder. This provides a decoder from the fine
observation. The assumption that the coarse data are obtainable is explicit.

Declaration: `recoverable_from_fine_of_coarse` (ObservationPrediction.lean).

### 9. Exact deterministic prediction requires compatible transitions

An exact predictor using only the current observation exists exactly when equal
current observations always yield equal next observations under the specified
deterministic transition. The two directions use the same consistency and
representative-selection reasoning as recovery. Iterating compatibility proves
agreement for all finite future steps. A next step that reveals an unobserved
bit supplies a counterexample when compatibility fails. These claims concern
exact prediction over all allowed states, not probabilistic accuracy from samples.

Declarations: `exact_predictor_iff`, `compatible_observations_agree_in_future`,
`same_current_observation_does_not_ensure_prediction` (ObservationPrediction.lean).
