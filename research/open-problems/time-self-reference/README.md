# Open problems in time, self-reference and changing systems

## Current direction — 25 September 2026

The user has redirected the main research effort toward **problems explicitly stated by the supplied papers**. The proposed unified minimal systems theory remains a motivating idea. We will discover which mathematical connections survive by working on the authors' questions.

The starting source is Abramsky, Banzhaf, Caves, Levin, Machado, Ofria, Stepney and White, *Open questions about time and self-reference in living systems*, Royal Society Open Science 13 (2026), 261059, DOI [10.1098/rsos.261059](https://doi.org/10.1098/rsos.261059). The user's published PDF has 29 pages; page numbers below refer to those PDF pages, which agree with the printed body pages. Its SHA-256 is `8b3940d8ac53c7145584c38c1a95a27c87f9c8173323112865c5439862bf43ce`.

The [author's institutional record](https://www-users.york.ac.uk/~ss44/bib/ss/nonstd/roysoc26.htm) and [earlier preprint](https://arxiv.org/abs/2508.11423) establish the bibliographic connection. Our question locators use the supplied published version, not an assumption that the preprint is identical.

## Follow the proof structure

Start with the [proof structure and remaining obligations](PROOF-STRUCTURE.md). It gives the source question, precise assumptions, conclusion, proof obligations, evidence, and residual gap for each active target. The [machine-readable problem ledger](problem-ledger.json) records the same status boundaries across all twelve source questions. Connections are marked as actual formal imports, shared proof methods, or biological analogies requiring further evidence.

## First completed results

- **Exact abstraction criterion:** checked necessary-and-sufficient condition, uniqueness and controlled-trajectory preservation, with a two-bit rule-hiding example. This is a formalization of established mathematics.
- **Merge-history obstruction:** checked four-component histories with the same unordered current partition and different next splits. It identifies missing information in a partition-only model of a predecessor-restoring split. An independent test executed the pinned original implementation's relevant function bodies with explicit constructor/scalar mocks and reproduced the same collision. Full policy scheduling and paper-to-code version equivalence remain unverified.
- **Verification:** two Lean 4.33.1 modules, 16 selected audited endpoints, clean compiler exits, no placeholder axioms. See [formal statements and scope](exact-abstraction/README.md), [independent model review](independent-rsos-review.md), and the accompanying receipts. Counts refer to audited declarations, not independent discoveries.
- **Calibration limit:** [a written exact statistical bound](CALIBRATION-BOUND.md), independently reviewed, with 15 rational-enumeration cases and 834 deterministic rules checked. This result is not Lean-verified and does not solve general evolutionary model calibration.

For a plain-language picture of the history obstruction:

| Same present grouping | How it formed | Next split restores |
|---|---|---|
| {a,b,c}, {d} | a merged with b, then their group merged with c | {a,b}, {c}, {d} |
| {a,b,c}, {d} | b merged with c, then a merged with their group | {a}, {b,c}, {d} |

The present grouping hides information required by this split rule. Retaining the relevant merge history removes this particular ambiguity. It does not certify a model of biological species or cognition.

## What counts as progress

Each problem gets four separate records:

1. **Source question:** the question the authors actually ask, with a locator.
2. **Precise target:** a theorem, counterexample, algorithm or empirical test with explicit assumptions.
3. **Evidence:** source reading, mathematical argument, executable experiment, or a reproducible Lean check.
4. **Residual gap:** what remains between the result and the original question.

A proof about a restricted model is a partial answer to a research question only when the model and the missing assumptions are visible. A new Lean proof of established mathematics is useful formalization, but does not establish a new mathematical discovery. No full author-stated open problem is recorded as solved at this checkpoint.

## First problem map

| ID | Authors' question or explicit gap, paraphrased | Published locator | What an answer requires | Current action |
|---|---|---|---|---|
| Q01 | Does a new concept of time arise with life? | §2.2, p.5 | Operational definitions and biological/physical evidence, plus any chosen formal model | Retain as a foundational research question |
| Q02 | Can a non-iterative physical process efficiently explore the vast space of possibilities? | §3.3, pp.8–9 | A model of computation, resource budget and success criterion; quantum state preparation must be counted | Clarify assumptions before claiming an impossibility or speedup |
| Q03 | Does self-reference require or imply natural time? | §4.2, pp.10–11 | Distinguish a static self-referential description from its execution and physical interpretation | Compare to the paper's own coalgebra and oscillation examples |
| Q04 | When can the process of generating a result not be separated from the result by projection? | §4.2, p.11 | Specify what the projection must preserve | Exact deterministic abstraction criterion and rule-hiding counterexample: Lean checked |
| Q05 | Which formalisms model systems that change their rules and interact with an environment? | §6 opening, pp.15–16 | Explicit syntax, update semantics, inputs and correspondence to the intended system | Separate state/rule dynamics from changes of modeling language |
| Q06 | How can practical tools support deeper changes of the modeling language itself? | §6.2.3, p.20; §7, p.24 | Specify interpretation, permitted language changes and retained invariants | Source and prior-art comparison; fixed interpreter remains an explicit assumption |
| Q07 | How should self-modifying open systems be analyzed when they outgrow a current model or metric? | §6.3, p.21 | Define a family of observables and a criterion for detecting inadequacy | Investigate information lost by a chosen observation/abstraction |
| Q08 | How can relational self-production models connect to plausible biological mechanisms? | §6.4.1, p.21 | A source-faithful mechanism and experimentally grounded correspondence | Needs a specific model; formal consistency alone is insufficient |
| Q09 | How should games represent decisions that merge or split the decision makers themselves? | §6.4.3, p.22 | Track membership, controller memory, actions, payoffs and what persists across a merge/split | Pinned implementation checked; merge-history obstruction Lean checked; whole game problem remains open |
| Q10 | Can rule-changing games retain the intended game-theoretic solution concepts? | §6.4.4, pp.22–23 | Specify the domain/powerdomain and the missing property of the solution concept | Read Vassilakis before proposing a replacement theorem |
| Q11 | Is representation foundational, or grounded in autonomous organization? | §7, pp.23–24 | Discriminate philosophical claims, operational criteria and mathematical definitions | Preserve as a conceptual question; no proof target selected |
| Q12 | How can evolutionary models be calibrated when observed histories cover very few possible outcomes? | §7, p.24 | Separate structural identifiability, finite-sample evidence and counterfactual extrapolation | Written rare-branch testing bound; identify what additional evidence can help |

This is a working inventory of this one paper, not a claim to have inventoried every question in every supplied PDF. The other seven recent papers are being read separately for explicit targets.

## Why these first targets

**Exact abstraction** gives a precise version of the user's “abstraction fee”: information discarded by simplification. The mathematical target concerns whether the compressed state contains enough information to determine its own next state under every allowed action. It does not yet measure the loss in bits.

**Changing decision makers** is the most direct connection to the user's parent/child and minimal-agent intuition. A merge/split model can describe changes in individuality, but a genealogical edge, a causal dependence and a game decision are different relations. Their correspondence must be defined and proved.

**Calibration** connects directly to the earlier ancestry work: an observation may fail to distinguish different histories or mechanisms. Here the immediate target is finite statistical evidence about an unseen branch; it does not assume the stronger claim that the models have the same full observation law.

## Relevant established mathematics

- Rutten's [Universal coalgebra: a theory of systems](https://ir.cwi.nl/pub/48) develops systems, behavior and structure-preserving maps. Quotient conditions are established mathematics.
- Shalizi and Crutchfield's [Computational Mechanics: Pattern and Prediction, Structure and Simplicity](https://arxiv.org/abs/cond-mat/9907176) establishes optimality/minimality results for predictive causal states. Predictive minimality always depends on a process and prediction task.
- Apt and Witzel's [A Generic Approach to Coalition Formation](https://arxiv.org/abs/0709.0435v3) treats merge/split transformations of partitions and conditions for stable outcomes. It is a concrete starting point for Q09. Its persistent underlying members and preferences must be compared with the biological model's changing controllers and payoffs before transferring any theorem.
- The source paper itself cites domain theory, coalgebra, self-modifying genetic programming, computational reflection, memory evolutive systems and earlier metabolism–repair models. We must build on those explicit connections.

These links identify usable prior work. They do not constitute a completed novelty search or show that the biological agenda is subsumed by existing results.

## Previous work remains available

The previous public baseline is [commit 414e79a](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/commit/414e79a02ac940da8cd89d58211c5a1fba760233), with its [Wong coverage map](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/414e79a02ac940da8cd89d58211c5a1fba760233/research/wong/completion/COVERAGE.md) and [successful hosted verification](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/actions/runs/36142086589).

Wong whole-paper formalization remains incomplete. Interval canonicalization was saved before its first compile; the absorption lane saved a checked scalar drift inequality and two uncompiled probability drafts. These are recoverable checkpoints, not completed absorption or canonicalization proofs. The checked MRCA truncation module is still awaiting public integration. The separate feedback task delivered a verified version-2 package, also awaiting integration at this checkpoint.

No task was archived. New work should be linked back to this index and carry its own verification status.
