# Independent review: time, self-reference, and changing players

**Disposition:** one source-grounded counterexample target is recommended. A bounded test of the pinned source operators with explicit mocks passed; this reviewer ran no Lean compiler or full simulation. It is a narrow result about sufficient model state, not a solution of the paper's biological agenda or an assertion of novelty.

## 1. Source and reading boundary

Samson Abramsky, Wolfgang Banzhaf, Leo S. D. Caves, Michael Levin, Penousal Machado, Charles Ofria, Susan Stepney, and Roger White (2026), *Open questions about time and self-reference in living systems*, Royal Society Open Science 13:261059, [DOI](https://doi.org/10.1098/rsos.261059).

Read from the supplied 29-page extraction at `friston-ancestry-feasibility/work/extracted/doc-8b3940d8ac53.pages.jsonl`. The underlying PDF SHA256 recorded in that sidecar is `8B3940D8AC53C7145584C38C1A95A27C87F9C8173323112865C5439862BF43CE`. The text extractor labels its output `extracted-unverified`; PDF page numbers agree with the visible printed page numbers in the text. All main-text pages 1–24 were read, and relevant references on pp. 25–29 were inspected. No second PDF extraction was performed. Missing special mathematical glyphs on pp. 17–18 were not interpreted as reliable equations.

This review distinguishes the authors' questions from the mathematical specifications proposed below. Page citations refer to the supplied published-paper extraction.

## 2. Six directly stated research questions

The short anchors below are exact contiguous phrases in the extraction; the question descriptions and candidate restrictions are paraphrases.

| ID | Source locator and short anchor | Authors' actual question or explicitly unresolved topic | What a finite theorem would and would not answer |
|---|---|---|---|
| Q1 | p. 10, §4.2; “possibility of self-reference” | Does self-reference require or imply natural time? | A theorem about indexed traces or projection can clarify a mathematical semantics. It cannot establish an ontological necessity for the authors' physical notion of natural time. |
| Q2 | pp. 15–16, opening of §6; “changes its own rules” | Which mathematical and computational frameworks model rule-changing systems open to their environment? | An operational semantics for a precisely specified model class is responsive. Merely storing one update rule in another rule's state does not establish unbounded novelty or a biological model. |
| Q3 | p. 20, final paragraph of §6.2.3; “dynamic metalanguage” | How can reflective languages generate changing models of open-ended systems, and how can languages themselves be dynamically generated? | A finite syntax/semantics with model-editing actions answers a restricted implementation question. The authors' stronger changing-language and continuing novelty requirements remain separate. |
| Q4 | p. 21, §6.3 heading; “appropriate analysis tools” | What tools can analyse changing, evolving, open systems when their current behavioural model may be outgrown? | Proving the scope of an invariant, quotient, or observation criterion can be useful. A fixed observer is not automatically adequate for all future model changes. |
| Q5 | p. 22, §6.4.3; “adding or removing selves” | Develop game theory in which participants' actions change the number and identity of decision-making individuals, including merging and splitting. | A theorem for a defined player-reconfiguration process directly addresses one part. Ordinary partitions alone do not specify decision authority, inherited policy, legal future splits, or how preferences survive a changed identity. |
| Q6 | p. 24, §7; “many fewer datasets” | How should evolutionary models be calibrated when many possible trajectories remain unobserved, without confusing unrealized possibilities with impossible ones? | A precise observational-equivalence or experiment-design result addresses identifiability for a chosen model class. It cannot infer which biological counterfactual model is true from insufficient evidence. |

Other explicit topics include non-iterative exploration of a large possibility space (§3.3, pp. 8–9), and whether representation is foundational or depends on autonomous organization (§7, p. 24). These are broader than a small Lean theorem.

## 3. Scope audit of three tempting formalizations

### Finite self-modifying systems

The paper does not state a finite-state conjecture whose solution would settle open-endedness. Its §5.5, pp. 14–15, distinguishes variation within a model from changes to models and languages. A closed deterministic system with a finite complete state—including all mutable code, interpreter state, memory, and environment variables—has an eventually periodic orbit. A nonperiodic external input invalidates that closed-system premise; an unbounded clock or memory invalidates finiteness. Proving eventual periodicity is a useful boundary result, but it does not settle the paper's broader novelty definition.

The assertion in p. 8 footnote 8 requires care. Self-modification by itself does not imply that the enlarged state has no fixed transition function. Rice-type undecidability also does not supply a general time lower bound for every finite-horizon trajectory. These are distinctions between model class, computability, running time, and external information; they should not be compressed into a single impossibility claim.

### Time-unrolling

The authors already discuss the time-indexed Boolean oscillator through Grim and colleagues (§4.2, p. 11, references 60–63); streams and coalgebra appear on p. 17, and Korbak's biological interpretation appears on p. 21, reference 144. Replacing a fixed-point equation by a recurrence specifies a different mathematical object. It does not prove the original unsatisfiable fixed-point equation satisfiable. A faithful result can characterize when forgetting time preserves an operation; an oscillator demonstration alone is neither new nor an answer to all of Q1.

### Diagonal prediction obstruction

No directly stated diagonal prediction conjecture was identified in this paper. A disclosed Boolean forecast that an agent is allowed to negate cannot be universally correct, under those explicit access and timing assumptions. That classical construction does not show that every self-referential finite system is unpredictable, that all forecasts must fail, or that time-indexing eliminates diagonal obstruction. It is a sharpened question proposed by us, not an open problem quoted from the authors.

## 4. What the coalition literature already supplies

[Apt and Witzel, *A Generic Approach to Coalition Formation*, arXiv v3](https://arxiv.org/html/0709.0435v3), §2, fixes a finite underlying set and studies merge/split transformations of its partitions. Its comparison relation is strict, transitive, and satisfies two compatibility conditions for adding disjoint collections. Note 2 derives termination; §6 Theorem 15 obtains a unique outcome under an additional stable-partition hypothesis. These hypotheses must be checked before transferring the results. [Publication record](https://dare.uva.nl/id/48721c48-8f21-4ff3-9590-c11e5e03e7e3).

Crucially, the prior work already permits comparing **whole coalition values** (§3); persistent individual payoff comparisons are another construction (§4). Therefore it would be inaccurate to dismiss that framework simply because the current decision makers are coalitions, or because their number changes. Neither would it be accurate to declare the biological question subsumed solely because both models have merge and split operations.

### Our proposed comparison contract

To determine whether a changing-self game reduces to a coalition model, make the following modelling choices explicit:

1. **Persistent substrate.** Specify a finite component set $`N`$, and say whether components can be born, die, move, or be replaced. A partition of fixed sites is not automatically a partition of persistent biological individuals.
2. **Current decision makers.** For each full state $`s`$, give a partition $`P(s)`$; its blocks, not necessarily the components, carry actions. Formally the action family can be indexed by $`B\in P(s)`$.
3. **Complete state.** Include every variable that can affect future transitions: current policies, memories, scores, spatial relations, environment state, and, when relevant, the history of earlier merges.
4. **Identity transition.** A merge/split operation must specify which old individuals persist, cease, or reappear, and how internal data are copied or reset. This is additional structure beyond the current collection of member sets.
5. **Cross-identity preference.** If a block $`B`$ disappears, an expression comparing its utility before and after that event needs a definition. Options include persistent-component utilities, a specified successor-weight map $`w_s(B,C)`$, or a directly defined state preference. These are different assumptions; none follows from the ability to merge.
6. **Reduction and stability.** First prove that the proposed reduced state determines the next reduced state or transition law. Only then test whether the permitted transitions respect one fixed strict comparison relation and the relevant compatibility/stability assumptions. Learning and changing preferences can violate these even when the substrate is finite.

This is an audit specification, not a claim that any one utility convention is biologically correct.

## 5. Primary implementation: an exact missing-state obstruction

The [Levin lab software page](https://drmichaellevin.org/resources/software.html) links the authors' [IPDm repository](https://github.com/lksshw/IPDm/), described as the implementation accompanying Shreesha et al. (2025), reference 150. I read the relevant source without installing or executing it. The reviewed commit is `eca9b122480b8c654081d6a844176417aefbbcae` (public API timestamp 2025-07-16T14:35:35Z).

At this commit, [the merge/split implementation](https://github.com/lksshw/IPDm/blob/eca9b122480b8c654081d6a844176417aefbbcae/core/helperfunctions.py#L111) stores both predecessor IDs in the newly created agent's `parents`. A split reactivates exactly those stored predecessors and deletes their composite. The new composite copies the better-scoring predecessor's policy and memory; its score is the average of predecessor scores. Split copies the composite's state back to its predecessors. Relevant lines: merge 111–145, parent construction 119, memory 125, score 129, policy 132, split 153–174. This is a history-sensitive operation, not an arbitrary subdivision of the current block.

The [board state](https://github.com/lksshw/IPDm/blob/eca9b122480b8c654081d6a844176417aefbbcae/core/env.py#L96) recovers active agents by following the merge forest from initial sites. The [main loop](https://github.com/lksshw/IPDm/blob/eca9b122480b8c654081d6a844176417aefbbcae/ipd-ms.py#L63) ends when no opponent remains. These details matter for a faithful witness.

### Actual bounded operator test

`independent-ipdm-operator-test.py` executed the original AST bodies of `merge`, `split`, six ancestry/neighbour helpers, and four original board methods at the pinned commit. Source hashes are checked before execution. Agent/Tree constructors and the two scalar NumPy helpers were replaced by explicitly listed mocks; all scores were zero, so rounding choices cannot change the witness. No package installation or complete simulation occurred. The actual command `python -X utf8 independent-ipdm-operator-test.py` returned exit code 0 and wrote `independent-ipdm-operator-test.json`, status `PASS_PINNED_OPERATOR_TEST_WITH_EXPLICIT_MOCKS`.

The test validates adjacent live merge operands, predecessor/child consistency, disjoint complete component support, correct active IDs, symmetric neighbourhoods, and equal visible pre-split data. The composite is a superagent and has the spectator as a live neighbour. It then invokes the same controlled split operator on both worlds and obtains the two different partitions below. The policy/fight process that emits the S action was not executed; those histories are operator-admissible, not asserted reachable under the complete stochastic scheduler.

### Recommended ONE target: current partitions do not determine the split operation

**Proposed formal model, sharpened by us from the actual source operation:** a finite forest of binary merge trees over four distinct component IDs $`0,1,2,3`$. Root trees are the currently active players. A merge replaces two roots by a parent; a split of a composite replaces it by its two immediate predecessor trees. The observation $`\pi`$ retains the current partition of component IDs. Optionally retain the active IDs and active policy/memory/score fields as well.

Construct the following admissible operator histories, using new IDs 4 then 5 in each:

```math
H_L:\quad (0,1)\longmapsto4,\quad (4,2)\longmapsto5;
```
```math
H_R:\quad (1,2)\longmapsto4,\quad (0,4)\longmapsto5.
```
Agent 3 is an unchanged spectator. In both final states, active IDs are $`\{3,5\}`$ and

```math
\pi(H_L)=\pi(H_R)=\{\{0,1,2\},\{3\}\}.
```
Split the same active ID 5. The outputs are

```math
\pi(\operatorname{split}_5(H_L))
=\{\{0,1\},\{2\},\{3\}\},
```
```math
\pi(\operatorname{split}_5(H_R))
=\{\{0\},\{1,2\},\{3\}\}.
```
The outputs differ because 0 and 1 belong to the same block in the first and to different blocks in the second. Therefore no deterministic map $`\bar S`$ on those observed states can satisfy

```math
\pi\circ\operatorname{split}_5=\bar S\circ\pi
```
on all admissible histories. The proof is an equality collision followed by different outputs. It should reuse the project's general exact-projection criterion if available, with this source-specific finite witness.

**Faithfulness details:**

- The four components fit the implementation's $`2\times2`$ grid with its eight-neighbour adjacency. The two merge sequences can use neighbouring active components.
- The spectator preserves a second active player, avoiding the main loop's one-player stopping condition.
- Using the same active IDs in both states prevents a trivial explanation based on relabelling.
- Identical initial policy, memory length, memory, score zero, and action-count zero make the active metadata match through the merge operators; copying identical policies is insensitive to tie-breaking. This equality passed in the explicit mock test. It is not an assertion about initialization probabilities or a sampled stochastic run.
- The theorem concerns the specified merge/split operators. It does not prove that both complete histories occur with positive probability under every initialization, learning parameter, or game scheduler.
- A nondeterministic partition abstraction may still overapproximate both possible splits. The obstruction is to an **exact deterministic** partition-only quotient uniformly across these states, not to all useful abstractions.

**Why this is useful:** it identifies a concrete piece of state that a game-theoretic treatment of the published model must retain, and a precise reason a ready-made partition theorem cannot be imported without checking the reduction. It does not posit any new biological property, and it does not require speculative definitions of consciousness or selfhood.

**Expected novelty status:** the general quotient criterion and history-dependence obstruction are standard. This particular witness is an application to the authors' operation semantics. Do not describe it as a new general theorem, as solving all of Q5, or as disproving the coalition-formation literature.

## 6. Required gates before claiming a result about Shreesha et al.

1. Read the full published article or an authenticated author preprint and verify that this commit's predecessor-based split is the model at issue. The [IEEE article](https://ieeexplore.ieee.org/document/10970107) was robot-gated in this bounded pass. The author-listed [OSF preprint](https://doi.org/10.31219/osf.io/kpzju_v2) was located, but the attempted OSF routes returned internal errors. The abstract and repository link do not settle version equivalence.
2. Decide whether the public theorem targets operator-admissible histories or histories reachable under the full learning and scheduling process. The former is immediately bounded; the latter needs additional reachability assumptions and work.
3. Prove the finite forest invariants, exact observation collision, different split partitions, and no exact quotient. No Lean compilation has been started for this task.
4. If an equilibrium or convergence theorem is later proposed, specify preference transport and check the literature's monotonicity/stability premises. The counterexample alone says nothing about existence of equilibria or convergence rates.

### Source reproducibility

Pinned source hashes, obtained read-only:

- `core/helperfunctions.py`: `edaacacbb6f09810c0acd9fcbf7642610695501952b04eb59fb0d6a7a2e7a5a4`
- `core/env.py`: `ecabd348002af771e7b07f6ba70aca281efd7f978e9643e33a896ad226cec886`
- `ipd-ms.py`: `c28666a35b61da89b82c7a0d7987a2e43baaf869b58a1b3fbd72f8a945a6d7e3`

The source code was read as text only. No repository was cloned, no simulation was run, and no public files were modified.
