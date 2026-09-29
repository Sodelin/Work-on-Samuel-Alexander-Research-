# Which stated open problems have been answered?

Audit date: 25 September 2026. This is a source and claim audit, with a bounded check of the current proof endpoints. It does not establish worldwide priority.

## Short answer

**The classification question Alexander asked in 2013 has a mathematical answer in the supplied September 2026 classification manuscript.** Our project verifies that construction, supplies an end-to-end binary classification theorem, and proves additional results. The construction and classification must retain their source attribution.

**Our quantitative Thue–Morse result does answer an explicitly stated question in that later manuscript.** Its all-start exact maximum formula strengthens the requested explicit bound. That question is not identified in the inspected sources as a question Alexander himself posed.

The current specieslike, reflection, degree-cap, and matching-height results do **not** justify saying that we have solved Alexander's remaining maximal-cluster, universal-avoider, or ordinal-characterization questions. Several of those results answer concrete extension questions developed during this project.

## 1. Source identity and attribution

| Source | Identifiable authorship and date | Location used |
|---|---|---|
| *Biologically unavoidable sequences* | Samuel A. Alexander; arXiv v2, 5 February 2013 | [§6, printed p. 9](https://arxiv.org/pdf/1212.0186v2#page=9); [HTML](https://arxiv.org/html/1212.0186v2#S6) |
| *Infinite graphs in systematic biology, with an application to the species problem* | Samuel A. Alexander; 2013 paper, inspected arXiv v7 | [§5.1, Open Problem](https://arxiv.org/html/1201.2869v7#S5.SS1), which also poses the vertex-gendered classification question |
| *Specieslike clusters based on identical ancestor points* | Samuel Allen Alexander; arXiv v1, 5 February 2026 | [§3.3, Informal Question 4; §6, Theorem 13 and following paragraph](https://arxiv.org/html/2602.05274v1); [PDF, especially pp. 9 and 16–18](https://arxiv.org/pdf/2602.05274v1) |
| *A classification of biologically unavoidable sequences* | Front matter dated **10 September 2026**, with no named author field. Its §7 credits an unnamed human collaborator's direction and OpenAI Codex's development. Alexander is credited for prior work. | [Pinned manuscript, §§1, 5, 7](https://github.com/avg-netizen/biological-unavoidability/blob/3d6175e3e23f67bd68e7be591b5a9a6d04e496a3/paper.md) |

The last manuscript is pinned to commit **`3d6175e3e23f67bd68e7be591b5a9a6d04e496a3`**. Repository ownership alone does not establish the identity of its unnamed human collaborator. We should describe it as the separate September classification manuscript, rather than invent a named human author or attribute its quantitative question to Alexander.

## 2. Exact source questions and present status

| Question | Exact source location and wording, or labeled paraphrase | Status of our work |
|---|---|---|
| Which sequences are biologically unavoidable? | Alexander 2013, §6, p. 9, final paragraph: **“Are there any which are not eventually periodic?”** | **Answered in the supplied later source.** The answer is no. Our work verifies and extends this solution; it does not originate the supplied construction. The [current binary real-birthdate endpoint](../../real/RealBridges.lean#L269) is an unconditional equivalence. The general finite-alphabet positive direction is not currently encoded by our project. |
| Useful explicit bounds for the fixed Thue–Morse target | September manuscript, §5, final sentence, [pinned lines 201–205](https://github.com/avg-netizen/biological-unavoidability/blob/3d6175e3e23f67bd68e7be591b5a9a6d04e496a3/paper.md#L201-L205): **“Obtaining useful explicit bounds for the fixed Thue–Morse target remains a quantitative question.”** | **Answered by our quantitative development.** A sharp linear bound, its complete equality set, and then exact maxima at every start are proved. This is a stated question from the separate September manuscript, not an identified Alexander-authored question. See §3 below. |
| Avoiding populations universal among all populations avoiding a fixed sequence | Alexander 2013, §6, p. 9, first paragraph. **Paraphrase:** seek an analogue of the universal-graph phenomena studied by Cherlin–Shelah. | **Not answered.** Realizing every word is a property of one graph's path language; being universal among avoiding graphs concerns a specified comparison or embedding relation between graphs. Our language-universality results do not supply that graph-universality theorem. |
| An ordinal characterization of populations realizing a sequence | Alexander 2013, §6, p. 9, second paragraph. **Paraphrase:** seek an ordinal description analogous to Schmidt's characterization of rayless graphs. | **Not answered in the intended generality.** We analyze matching heights and related ranks in particular constructions. A general characterization of arbitrary eligible populations, with the exact rank convention and reconstruction content specified, has not been proved. |
| Further constraints ensuring maximal specieslike clusters, especially without a common ancestor requirement | Alexander 2026, §6, p. 17, paragraph immediately after the proof of Theorem 13. He particularly seeks a solution **“not requiring the CA property.”** | **Not answered by our reflection lemma.** That lemma assumes an existing unrestricted maximal specieslike cluster. It supplies no general existence theorem or new coverage theorem ensuring each organism belongs to an appropriate maximal cluster. The productive-core species theorem also has a whole-population identical-ancestor-point premise. |

Alexander's broader **Informal Question 4** in §3.3 is already answered under his own common-ancestor and reflection conditions by **Theorem 13**, pp. 16–17. The further question is about different sufficient constraints, particularly removing the need for the common-ancestor condition. These two stages must not be collapsed into a claim that his paper leaves all maximal-cluster existence untreated. [Alexander 2026](https://arxiv.org/pdf/2602.05274v1#page=16)

## 3. What answers the quantitative question?

Let $`t`$ be the Thue–Morse sequence, $`P_t`$ the supplied binary avoiding graph, and $`L(v)`$ the greatest number of edges of a finite path starting at $`v`$ whose labels match the unshifted target $`t`$.

For every positive starting vertex, the proved sharp bound is

```math
3L(v)\le 8v-1 \qquad (v\ge 1).
```

The full equality set is

```math
3L(v)=8v-1
\quad\Longleftrightarrow\quad
\exists n\in\mathbb N:\quad
v=3\cdot2^n-1,\qquad L(v)=8\cdot2^n-3.
```

The proof applies to actual matching paths, and proves that the maximum is attained. It is stronger evidence than a finite computational scan:

- [SharpThueMorse.binary_path_prefix_bound](../../lean/SamuelAlexanderResearch/SharpThueMorse.lean#L417) connects the inequality directly to the source graph's edge relation.
- [SharpThueMorse.sharp_equality_indices](../../lean/SamuelAlexanderResearch/SharpThueMorse.lean#L424) identifies every equality case.
- [FullHeight.height_isMaximum](../../lean/SamuelAlexanderResearch/FullHeight.lean#L46) and [height_closed_form](../../lean/SamuelAlexanderResearch/FullHeight.lean#L915) give exact actual-graph maxima at **every** natural start, including zero.
- [DigitRecurrence.actual_digit_recurrence](../../lean/SamuelAlexanderResearch/DigitRecurrence.lean#L432) and [evaluate_isMaximum](../../lean/SamuelAlexanderResearch/DigitRecurrence.lean#L444) provide an unconditional ten-coordinate binary recurrence and certified evaluator. Neither final endpoint assumes `FormulaSpec`.

This computes a graph-specific maximum. The ten coordinates are integer values, so this is not a claim that ten finite states suffice. Minimal representation dimension and a formal complexity bound do not follow just from these endpoints. The separate Mathlib statement about finite generation of the binary kernel remains outside this audit.

## 4. Useful project extensions, with their boundaries

| Result | What is proved | What this does not settle |
|---|---|---|
| Optimal binary degree cap with fixed source gender | [CapTwo.avoiding_population_exists_iff](../../lean/SamuelAlexanderResearch/CapTwo.lean#L295): an eligible fixed-gender population of child cap $`d`$ avoiding $`s`$ exists exactly when $`d\ge2`$ and $`s`$ is not eventually periodic. | No source-stated Alexander question about this optimal cap was identified. This is a project extension, with global novelty unsettled. It concerns the stated binary population axioms. |
| Avoidance within a specieslike inspecies | [CapTwoSpecies.cap_two_inspecies_avoider](../../lean/SamuelAlexanderResearch/CapTwoSpecies.lean#L102): the cap-two witness satisfies specieslike, inspecies, and reflection properties in its actual induced graph. | It gives a mathematical witness satisfying these definitions. It is not an empirical species classification, or a general existence theorem for species in every genealogy. |
| Productive pruning | [ProductiveCore.productive_core_theorem](../../lean/SamuelAlexanderResearch/ProductiveCore.lean#L400): under the displayed whole-population IAP premise, the reindexed core is eligible, retains the cap, is an inspecies, and preserves avoidance. The separate language theorem proves exact infinite-language preservation. | The IAP premise is substantial; the species conclusion is not unconditional for all populations. |
| Unrestricted maximal clusters reflect productivity | [maximal_specieslike_descendantClosed](../../lean/SamuelAlexanderResearch/ProductiveCore.lean#L517) and [maximal_specieslike_reflection](../../lean/SamuelAlexanderResearch/ProductiveCore.lean#L582), under strict natural birth order. | Maximality is over all specieslike supersets and existence is assumed. It is not maximality inside Alexander's four-condition class, and not maximality restricted to proper ambient subsets. |
| Constrained-maximal counterexample | [constrained_maximum_not_descendantClosed](../../lean/SamuelAlexanderResearch/ProductiveCore.lean#L738) prevents that maximality distinction from being silently dropped. | Alexander's own Example 14(2), p. 17, already supplies the relevant two-branch mechanism. A formal counterexample is not evidence that this phenomenon was missing from his paper. |
| Matching-tree heights and rank comparisons | The finite-start matching trees in an avoiding, finitely branching population have finite height; a forest over unbounded starts can have an aggregate ordinal behavior different from a single tree. | These objects and ranks must be named precisely. Such observations do not yield the general ordinal characterization Alexander requested. He already cites the relevant universal-graph and rayless-graph literature in §6. |

Related older species facts also need attribution. Alexander's 2013 systematic-biology paper, Definition 4 and Proposition 6, already develops inspecies and the cofinite-descendant property. Our source audit finds that the older avoiding constructions have the relevant whole-inspecies behavior; packaging that implication explicitly is not sufficient evidence of a new biological principle. See [older-construction and rank audit](OLDER-CONSTRUCTIONS-AND-RANK-AUDIT.md) and [maximal-specieslike source audit](MAXIMAL-SPECIESLIKE-SOURCE-AUDIT.md).

## 5. Safe summary for a handoff

> We formalized and extended the supplied classification construction. Our quantitative work answers the later manuscript's explicit Thue–Morse bound question, with a sharp inequality and exact maxima. We also proved optimal binary fixed-gender degree bounds and structural pruning and reflection results. We have not established a new solution to Alexander's general maximal-cluster existence, universal-avoider, or ordinal-characterization questions, and we do not claim worldwide priority for these extensions.

The project's “ten solutions” are answers to its own ten extension proposals. They should not be advertised as ten previously open problems posed by Alexander. The mathematics remains useful when described with these distinctions intact.

## 6. Verification scope and documentation drift

This pass read the source questions and current theorem statements; it did not run a new Lean build. The current SHA-256 hashes of `CapTwo.lean`, `CapTwoSpecies.lean`, `ProductiveCore.lean`, `SharpThueMorse.lean`, `FullHeight.lean`, and `DigitRecurrence.lean` match the stored [370-endpoint Std audit](../../verification/formal-audit.json), timestamp **2026-09-25T08:13:42.736075+00:00**. Its admitted logical dependencies are the ordinary Lean axioms `propext`, `Classical.choice`, and `Quot.sound`; this is not a new proof or a complete dependency recheck in this pass.

`real/RealBridges.lean`, containing `binary_real_classification`, also matches its hash in the stored [19-endpoint real audit](../../verification/real-audit.json), timestamp **2026-09-25T06:35:10.693788+00:00**. That bounded source-hash check is separate from any additional Mathlib modules currently being developed.

At inspection, `TEN-SOLUTIONS.md` and `STATUS.md` described completed cap-two and full-height results. `QUESTION-LEDGER.md` and `HANDOFF-FOR-ALEXANDER.md` still contained earlier open/conjectural descriptions of those results and related extensions. Those discrepancies were reported to the coordinating task for correction. No implementation-owner files were edited by this audit.
