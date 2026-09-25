# Exploratory interface: lineage graphs and dynamical emergence

**Status and priority:** exploratory model design, parked outside the repository's main result table. The comparison cites existing research, but the proposed interface is ours. It is neither a theorem connecting Alexander, Levin, and Friston nor a Lean verification of their biological theories. No implementation lane is opened until a specific state-to-lineage map and testable question are chosen.

## Related mathematical questions with different answers

| Work | Main object | Typical mathematical question | What it leaves unspecified |
|---|---|---|---|
| [Alexander 2013](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v20i1p31) and the [2026 classification manuscript](https://github.com/avg-netizen/biological-unavoidability/blob/main/paper.md) | An infinite, birthdate-ordered parenthood graph with labels on parent edges. | Which infinite label words occur in **every** admissible graph? | Cell state, inherited phenotype, probabilities, selection, and a mechanism of species formation. |
| [Alexander 2026, specieslike clusters](https://arxiv.org/html/2602.05274v1) | Subsets of an unlabelled genealogical graph. | Which ancestry-based axioms make a subset a coherent cluster, and when do maximal such subsets exist? | A unique empirical species boundary, traits, and an explicit update law for evolution. See the [direct graph bridge](../notes/SPECIESLIKE-BRIDGE.md). |
| [Manicka and Levin 2025](https://doi.org/10.1016/j.xcrp.2025.102865) | Voltages and other states of electrically coupled cells. | Can local currents and feedback generate a spatial voltage pattern? | The parent-label axioms of Alexander's infinite population, and an automatic definition of species. The [authors' code](https://github.com/santamanicka/ElectricMorphogenesis) is simulation, not a proof of every possible tissue behavior. |
| [Friston and coauthors' review](https://arxiv.org/html/2201.06387v3) | Stochastic dynamics, probability distributions, Markov blankets, and variational objectives. | Under stated assumptions, how do probability and inference quantities relate to a system's states and policies? | An ancestry graph or a theorem about every possible lineage word. |

Your intuition points toward a **new interface between these objects**, not an identity between them. For example, the vertices in Levin's model are interacting cells in a tissue; the edges carry electrical coupling. Alexander's vertices are organisms across birthdates; the edges carry parental roles. A map between the two must be defined and its hypotheses checked.

## A candidate model for “an emergent property”

Here is one explicit way to turn the question into mathematics. At each time `t`, let `X_t` be a configuration of microstates (cell voltages, cell fates, or agent choices). Let an update rule `F` or stochastic transition kernel `K` produce the next configuration. Let `M(X_t)` be a chosen macro-observable, such as tissue shape or a group-level convention. Specify a target set `A` of macro-observables and a class `P` of allowed perturbations.

A strong deterministic version of **robust recovery** might be:

```text
For every starting state x in a specified basin B and every perturbation p in P,
there is a finite recovery time T such that M(F^t(p(x))) is in A for all t >= T.
```

For a stochastic system one would instead specify a time horizon, a probability threshold, and a distribution of perturbations. Neither definition is canonical. Choosing `M`, `A`, `B`, and `P` is part of the scientific model, and a real experiment would test whether they correspond to observable biology or social behavior.

**A finite toy, to show the logical difference.** Let a system have three Boolean cells. At each step, set all three to the majority of their previous values. After one step every cell agrees; that all-agree state is fixed. If one bit of `000` or `111` is flipped, one update restores the original all-agree state. This is a tiny example of a robust *macrostate*. It says nothing about actual morphogenesis, speciation, or human societies. Alexander's path theorem alone does not imply it: one must specify the majority update rule. Conversely this toy's stability says nothing about infinite parent-label paths. A future Lean exercise could formalize those finite claims as a transparent interface test, explicitly separate from the cited theories.

To link such a system to Alexander, **unfold it through time**: represent a component at each time as a vertex, choose what cross-time influence or parenthood means, and choose a label observable. Then check, rather than assume, finite roots, finite birthdate prefixes, finite outdegree, and one incoming edge of every label at each nonroot. A tissue's electrical-neighbor graph or a social influence network may fail these assumptions. If they fail, one could state a new graph theorem for the appropriate axioms; the original unavoidable-sequence classification does not automatically transfer.

## Where differential equations and chaos fit

This part of the user's intuition is right for **some** descendants. A continuous-time cell-state model may use an ODE such as `C_i dV_i/dt = I_i^ion + sum_j G_ij(V_j-V_i)`; the cited Levin model also uses an explicit time-step simulation and field feedback. Friston's review begins with stochastic differential dynamics and uses probability identities. A finite or discrete social model might instead use update maps or stochastic transitions. Alexander's sequence and cluster theorems are combinatorial statements about graphs and quantifiers, with no differential equation in their hypotheses.

An aperiodic word is not automatically chaotic. Chaos requires a specified dynamical system and a sensitivity or entropy property; the classification merely distinguishes eventual periodicity of a target sequence. Feedback, an attractor, and a specieslike lineage are also different predicates. One can study them together after defining the state-to-genealogy interface, but no theorem here equates them.

## What Lean has and has not checked

- **Alexander work in this repository:** [our Lean module](../lean/SamuelAlexanderResearch/DegreeBounds.lean) checks arithmetic consequences from count premises. The [classification repository](https://github.com/avg-netizen/biological-unavoidability/blob/main/STATEMENT-AUDIT.md) reports a Lean endpoint for its avoiding construction, with stated scope. The specieslike bridge above is a prose proof and has no Lean encoding here.
- **Friston-related mathematics:** [Mathlib's KL-divergence library](https://leanprover-community.github.io/mathlib4_docs/Mathlib/InformationTheory/KullbackLeibler/Basic.html) and the [Active Inference Institute's Lean catalogue](https://github.com/ActiveInferenceInstitute/fep_formal) contain substantial formal work. That project's own [coverage and scope report](https://github.com/ActiveInferenceInstitute/fep_formal/blob/main/docs/formalism-coverage.md) distinguishes checked finite probability, variational, blanket, and selected dynamical results from proxies and unproved physical or empirical claims. We inspected its published scope; we did **not** independently build its repository. The elementary variational identity `F(q,o) = -log p(o) + KL(q || p(h|o))` depends on ordinary positivity and support assumptions and does not by itself prove a universal biological principle.
- **Levin's cited bioelectric model:** a focused source and repository search found [Python simulation code](https://github.com/santamanicka/ElectricMorphogenesis), but no public Lean formalization of this **specific model**. That is a search result, not proof of absence. A meaningful first Lean target would isolate symmetric nonnegative gap-junction currents and prove conservation of total weighted voltage/charge under their update, with exact timestep assumptions. That would verify one mathematical subsystem, not the full biological interpretation.
- **The proposed cross-scale interface:** no Lean theorem yet. Formalization should start with one precise update rule and one state-to-lineage map, then test whether the graph axioms hold. A compiled toy lemma would not validate a general theory of complex adaptive systems.

## Two possible research descendants

1. **Genealogical descendant:** characterize the interaction between specieslike subsets and path-label coverage. The [direct bridge](../notes/SPECIESLIKE-BRIDGE.md) already shows the whole avoiding graph can be specieslike, while Alexander's stronger common-ancestor constraint changes the problem. An exact next task would define a subset's boundary and test which parental-label axioms survive restriction.
2. **Dynamical descendant:** choose a concrete small tissue or agent model, define a macro-observable and perturbation class, and prove or refute robust recovery. Then build its time-unfolded graph and check whether a lineage-word theorem can say anything additional. This route is much closer to Levin and Friston; a biological or social interpretation would require separate empirical validation.

The two descendants could meet at a **defined interface** between evolving state and ancestry. Until then, this is a source-backed idea map rather than part of the core proof program.

## A later psychology application, kept separate from the current handoff

The owner's longer-range interest is whether formal methods could make *particular* psychological claims easier to inspect and reproduce. A tractable first project would choose one measured construct, one instrument or dataset, and one explicit inference. Write down the raw responses, missing-data rule, scoring transformation, probability or causal assumptions, and the claim the analysis supports. Lean could verify properties of the scoring function or a theorem about a specified statistical model; separate empirical work would test whether the instrument tracks the intended construct, behaves comparably across groups, and predicts observations. [Borsboom, Mellenbergh, and van Heerden](https://doi.org/10.1037/0033-295X.111.4.1061) discuss why psychological measurement validity is a substantive question, not merely a correct calculation.

Friston's framework might supply a model of within-person inference or action; Levin's work might motivate a multiscale biological mechanism; Alexander's graph theory might help only after a psychology-specific lineage or influence graph has been defined and its axioms checked. None is a general mathematical validation of psychology. This is a future scoped program, not an additional task for the current Alexander proof sprint or part of the proposed first email to him.
