# Checked mathematics for ancestry, observation and biological modeling

Publication guide, 29 September 2026. Prepared by the human-directed Codex research project. This guide identifies the results, their mathematical value, their proof evidence and their relation to existing biological questions. It is an editorial reading route through the linked proof sources, not a substitute for them.

## What deserves attention

The strongest thread through these results is an explicit account of **which information determines a biological-model conclusion**. A fully specified finite sampling model can reverse a deterministic barrier comparison. Complete genome-copy transmission data can fail to determine an organism-level ancestry property. Carefully timed additional observations can repair that ambiguity in a declared family. An observable family-recovery estimator has an exact success formula, with a counterexample showing why independent inheritance blocks matter.

These statements earn their strength from their hypotheses and conclusions. Their value is not measured by the number of Lean declarations: supporting lemmas, reused results and audit reports are not separate discoveries. The technical work varies. The constrained ancestry construction must preserve several natural pedigree properties at once; the barrier result must connect an exact finite kernel certificate to a limiting probability; the sampling criterion is an elementary but sharp deduction once its family is constructed. We do not describe all three as equally difficult.

| Result or body of work | Concrete contribution | Publication disposition at this checkpoint |
|---|---|---|
| Finite-population genetic/epigenetic comparison | Exact fixation certificates establish the specified finite-model reversal. | Submitted to VibeMathed; confirmed in the review queue. |
| Same genome-copy history, opposite IAP | Constrained diploid constructions disagree on the identical-ancestor property despite identical complete copy-transmission observations and any prescribed finite ownership prefix. | Submitted to VibeMathed; confirmed in the review queue. |
| Ownership sampling | Exact criterion for which static observation times identify IAP within that construction family. | Submitted as its explicitly related continuation; confirmed in the review queue. |
| Sampled-family recovery | Exact finite-sample success probability for observed-symbol connected components, with a dependence counterexample. | Submitted to VibeMathed; confirmed in the review queue. |
| Exact Thue–Morse heights | Existing sharp all-start theorem; later exact finite-edit optimum and phase maxima. | Original entry already public; continuation posted in its discussion. |
| Merge/split memory obstruction | Same current player membership can require different predecessor-restoring splits. | Published here as a modest source-specific application; no separate new-discovery entry submitted. |
| Predictive state and stochastic abstraction | Checked contracts, source correspondence and reproducible counterexamples using established mathematics. | Public proof package and research infrastructure; no separate novelty claim. |
| Marked ancestral recombination graph (ARG) construction and pedigree bridge | Checked source-model construction and explicit conditions for transfer to organism ancestry. | Frozen proof package now public; known source mathematics is credited. |
| Other graph, word and cellular-automaton extensions | Exact theorem inventory below, including counterexamples and precise restrictions. | Public research results and supporting theory; no claim that each solves an externally posed open problem. |

VibeMathed submission means **received for editorial review**, not accepted, published, independently expert-verified or peer-reviewed. The public [review queue](https://vibemathed.com/queue) records pending titles. Candidate entries request “Partial result” and “Lean-checked, statement unaudited.” Priority and catalogue eligibility remain matters for external assessment.

## Connection to the biologists' open-questions paper

The primary agenda is Abramsky, Banzhaf, Caves, Levin, Machado, Ofria, Stepney and White, [*Open questions about time and self-reference in living systems*](https://doi.org/10.1098/rsos.261059), Royal Society Open Science 13, 261059 (2026). An [accessible preprint](https://arxiv.org/abs/2508.11423) is also available. The project read the published 29-page PDF; its SHA-256 is `8b3940d8ac53c7145584c38c1a95a27c87f9c8173323112865c5439862bf43ce`.

The paper does not state the project's twelve working targets as twelve numbered conjectures. **No full author question is recorded as closed.** A precise theorem about a chosen observation model is useful progress without being a solution of the paper's whole biological or philosophical question.

| Published source locator | What our work contributes | What is still needed |
|---|---|---|
| Section 4.2, p.11: process/result projection | Exact deterministic and discrete stochastic preservation contracts; concrete failures when required information is discarded. | A justified biological state, observation and intervention map; approximation or continuous kernels when required. |
| Section 5.2, p.13, and section 7, p.23: memory and path-dependent variables | An arbitrary-history parity model, the exact predictive quotient and explicit intervention-relative memory requirements. | Measured biological mechanisms and a validated correspondence; the Boolean “cell” is a stipulated model. |
| Section 6.3, p.21: recognizing model inadequacy | Constrained ancestry ambiguity, informative sampling criteria and predictive-equivalence counterexamples provide explicit tests under declared contracts. | Evidence that the selected model class, measurements and interventions apply to an organism. |
| Section 6.4.3, p.22: decisions merging or splitting decision makers | A legal-history witness showing that current membership alone cannot implement a predecessor-restoring split. | A complete game, including controllers, memory transfer, payoffs and a solution concept. |
| Section 7, p.24: calibration from sparse histories | Exact recovery probabilities and dependence failures in specified models; a separate written sharp impossible-versus-rare testing bound. | General evolutionary sampling, dependence and error assumptions, and empirical calibration. |

The barrier comparison is primarily motivated by Planidin et al.; the pedigree constructions use Alexander's ancestry definitions; the family estimator is motivated by Kim et al. The Royal Society paper provides related questions about observation, modeling and calibration. It is not credited with posing these exact specialized theorems. The [current source-to-result audit](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/da67b295530e175c8015a2151f30827ae2a5ad01/research/open-problems/time-self-reference/predictive-memory/AUDIT.md) gives the full twelve-target map and preserves every remaining gate.

## Individual result dossiers

Each dossier supplies a plain-language contribution, an exact target, a fuller result statement and the evidence boundary. All formalization claims concern the stated mathematics; they do not supply empirical biological validation.

### Finite offspring sampling reverses a genetic-epigenetic barrier ordering

**Why this is useful.** Deterministic averaging can conceal a qualitative effect of finite reproduction. The result supplies an exactly checked comparison in a specified small-population life cycle, so a reader can identify which modeling choices cause the change instead of relying on a simulation plot. The demanding step is identifying the actual limiting fixation probability from the finite kernel; the biological interpretation still depends on the declared life cycle.

**Precise question.** Planidin et al. (2025) study a deterministic model of adaptive epigenetic divergence and identify finite-population extensions as future work. In an explicitly specified finite offspring-sampling extension, can pure environmental induction yield a larger neutral-marker fixation barrier than the matched genetic model? The narrow target here fixes one diploid adult per deme, two demes, migration m=1/4, selection s=1/2, recombination r=1/2, matched secondary-contact initialization and a single preselection migrant-marker pulse. It is a project-formulated special case of that research direction, not a conjecture stated verbatim by the authors.

**Result and boundaries.** Contribution: a certified example in which a biologically motivated model change reverses the genetic/epigenetic barrier ordering. The proof connects exact rational transition identities to the actual limiting fixation probability, so the comparison is stronger than a numerical simulation. 

Yes, in this finite model. The limiting global marker-fixation probabilities are p_gen=323808055/4466354606 and p_epi=1/14. With the specified preselection dose B0=1/8 and RI=1-p/B0, RI_gen=937945083/2233177303 and RI_epi=3/7, so RI_epi-RI_gen=19130904/2233177303>0. A finite Markov-kernel harmonic certificate proves the actual marginal-probability limit with error at most (99/100)^n. The pure-induction scalar benchmark, finite stochastic epigenetic models, timing sensitivity and normalized marker fixation have prior literature.

The candidate incremental contribution is this exact matched comparison under the declared sampling and life-cycle assumptions. The phased-to-count-model correspondence has exact rational checks and written review; the Lean theorem begins with the explicit 81-state count model. There is no universal population-size ordering, validated species-formation mechanism or solution of the authors' whole research programme. The connection to Abramsky et al. is methodological: specify what survives a model change and what finite observations calibrate; it is not a solution of their questions. The separately checked RankingReversal.matched_reversal theorem places the finite genetic barrier below 3/7 while the matched deterministic genetic barrier is above 3/7 from biological generation four onward. This compares the finite long-run quantity with the stated deterministic finite-generation sequence; it does not claim an unproved strict inequality between their limiting values.

**Proof evidence.** Lean 4.33.1 with pinned Mathlib. The combined packet records 34 selected declarations across four modules, including the finite comparison and separate deterministic/joint comparison; declaration totals include supporting lemmas. The finite probability certificate uses kernel-checked integer identities, without sorryAx, custom axioms or native_decide. The combined local receipt preserves recovered exit evidence, and the later hosted Verify run 36173386580 succeeded at the submitted commit a2644182b147eb40816abb278e00c3c6d4709eb8. Its standalone audit includes this packet. Only propext, Classical.choice and Quot.sound are allowed. Source/statement review was internal to the project. Independent human review and priority remain unestablished; requested status is Partial result and Lean-checked, statement unaudited.

**Primary result:** [Read the full mathematical note](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/a2644182b147eb40816abb278e00c3c6d4709eb8/research/feedback-speciation/finite-epigenetic/FINITE-RESULT.md).

- [Source biology paper and finite-population direction](https://pmc.ncbi.nlm.nih.gov/articles/PMC12440623/)
- [Exact count-kernel Lean proof](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/a2644182b147eb40816abb278e00c3c6d4709eb8/research/feedback-speciation/finite-epigenetic/FiniteEpigenetic.lean)
- [Finite fixation theorem](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/a2644182b147eb40816abb278e00c3c6d4709eb8/research/feedback-speciation/finite-epigenetic/FiniteFixation.lean)
- [Matched deterministic/finite ranking theorem](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/a2644182b147eb40816abb278e00c3c6d4709eb8/research/feedback-speciation/finite-epigenetic/RankingReversal.lean)
- [Successful hosted verification](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/actions/runs/36173386580)
- [Prior-work and attribution boundaries](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/a2644182b147eb40816abb278e00c3c6d4709eb8/research/feedback-speciation/PRIOR-ART-UPDATE-2026-09-25.md)
- [Related open-questions agenda; a methodological connection](https://doi.org/10.1098/rsos.261059)

### Identical genome-copy transmission histories with opposite organism-level IAP

**Why this is useful.** The counterexample tests a tempting inference: that a complete molecular transmission record must settle the organism-level ancestry question. It does not in this declared observation model. The construction retains diploidy, connectivity, witnessed edges, degree constraints and arbitrarily long initial ownership agreement simultaneously. That conjunction is the candidate incremental contribution; pedigree ambiguity itself is established prior mathematics.

**Precise question.** In Alexander's specieslike-cluster framework, does a complete realized genome-copy transmission graph, together with any bounded prefix of organism ownership, determine the whole-population identical-ancestor property (IAP)? Consider the explicit class with four diploid organisms per generation, two distinct parents and two children per nonfounder/organism, witnessed parent-child edges and real generation birthdates. This inverse-observation question is a project-formulated follow-up; Alexander's source defines IAP and specieslike clusters but does not state this exact constrained question. Here IAP means that each organism has either finitely many descendants or finitely many non-descendants within the population.

**Result and boundaries.** Contribution: a constrained counterexample showing exactly why complete copy-transmission information can still fail to determine organism-level ancestry. The construction retains exact witnessed parent-child edges, diploidy, fixed degree bounds, connectivity and arbitrarily long agreement of ownership; the conclusion therefore survives those natural attempts to remove the ambiguity. 

No. One fixed graph consists of eight genome-copy lanes, advancing one generation per edge with the same interval [0,1). For every finite N, two diploid ownership schedules agree through N and preserve every recorded copy, date, interval and transmission. Both induced pedigrees are connected, have four organisms per generation, two copies per organism, two distinct parents per nonfounder, two children per organism and exactly witnessed pedigree edges. One whole population has IAP and is a maximal specieslike cluster; the other fails IAP after a delayed permanent split. This rules out an exact decoder of IAP from the specified complete unpaired history plus bounded ownership information on this family. The finite truncations map to the repository's Wong gARG structure. Preserving parent-child edges does not supply ancestry path lifting.

This is deterministic observational ambiguity, not equality of genotype likelihoods, positive probability of the infinite schedules, general statistical non-identifiability or a biological species classifier. The connection to Abramsky et al. concerns information lost by projection and model adequacy; their full author questions remain open.

**Proof evidence.** Fresh Lean 4.33.1 build of 31 project modules and axiom audit of all 77 new public theorem declarations at proof-source commit 1ba951e4417c930e76ef0f5ace747c9ccb681338. Published evidence head is 4ab00a2932f3efdb7091c9a526af4bcd25cc8cd2. Hosted Genome pedigree proofs run 36298049178 and Verify run 36298049071 both succeeded at that head. The 31 pinned source hashes were compared with the saved proof receipt on 29 September 2026 and all match; that comparison was not a new compiler run. No proof placeholders or nonstandard axioms; allowed axioms are propext, Classical.choice and Quot.sound. Internal mathematical/source reviews are not independent human review. The bounded prior-work search found no exact matching conjunction, but priority remains unestablished.

**Primary result:** [Read the full mathematical note](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/4ab00a2932f3efdb7091c9a526af4bcd25cc8cd2/research/genome-pedigree/README.md).

- [Alexander's IAP and specieslike-cluster definitions](https://arxiv.org/html/2602.05274v1)
- [Constrained construction in Lean](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/4ab00a2932f3efdb7091c9a526af4bcd25cc8cd2/research/genome-pedigree/PairingCore.lean)
- [Source-model bridges](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/4ab00a2932f3efdb7091c9a526af4bcd25cc8cd2/research/genome-pedigree/PairingBridge.lean)
- [Hosted proof replay](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/actions/runs/36298049178)
- [Prior-art and observation-model comparison](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/4ab00a2932f3efdb7091c9a526af4bcd25cc8cd2/research/genome-pedigree/PAIRING-PRIOR-ART.md)
- [Open questions about time and self-reference: related projection/adequacy agenda](https://doi.org/10.1098/rsos.261059)

### An exact ownership-sampling criterion for delayed-split identical ancestry

**Why this is useful.** Once a missing-information obstruction is known, the constructive next question is which measurement repairs it. This theorem answers exactly for the declared family. Infinitely many observations at even generations remain uninformative, while a single suitably timed query can suffice after a switch-time bound is supplied. It is a sharp model-specific measurement result, not a general algorithm for deciding infinite ancestry.

**Precise question.** Within the checked mixing-versus-delayed-splitting diploid family, which static sets of co-ownership observation times determine whole-population IAP from the complete observation record? At time t the query asks whether copy lanes 0 and 3 belong to the same organism. This is a project follow-up to the same-genome/opposite-IAP construction, motivated by Alexander's ancestry definitions and the open biology agenda's model-adequacy questions.

**Result and boundaries.** Contribution: an exact answer to which extra observations repair the preceding ambiguity within its declared family. It distinguishes informative sampling from observation volume: even infinitely much ownership data at the wrong generations can fail, while one well-timed observation suffices under a known switch bound. 

For this family, the complete record determines IAP exactly when the sampled odd generations are unbounded. The query is always false in the mixing pedigree and true in a splitting pedigree exactly at odd generations after its even switch time. Even the entire ownership assignment at every even generation fails to determine IAP. One positive query certifies splitting within the family; any finite collection of negative queries permits a later split. If a prior even bound B>=2 guarantees that any split occurs by B, a single query at B+1 suffices, and a static sampling set identifies IAP exactly when it contains an odd generation after B.

The infinite-record decoder is not a uniformly terminating decision algorithm. Finite/infinite monitoring distinctions and pedigree ambiguity are established; the incremental deduction is this exact mask criterion in the specified family. The observations do not justify the switch bound or biological model themselves.

**Proof evidence.** Local exact-clean-commit Lean 4.33.1 audit at c071d4b895b8fe979211b68ac30240f8833e707d: five project modules and 20 selected axiom reports, comprising 15 new observation endpoints and five reused construction endpoints. Evidence checkpoint is 35a8f86b5f0e555eab25d003353c0c8772578db5. The saved-evidence checker passed on 29 September 2026, confirming committed source hashes, compiler logs, 22 artifact hashes and the permitted standard axioms propext, Classical.choice and Quot.sound. This was receipt verification, not a new compiler run or a new hosted replay. Internal review and bounded prior-work comparison are recorded; independent human review and worldwide novelty are not claimed.

**Primary result:** [Read the full mathematical note](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/35a8f86b5f0e555eab25d003353c0c8772578db5/research/owner-observations/README.md).

- [Exact sampling criterion in Lean](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/35a8f86b5f0e555eab25d003353c0c8772578db5/real/PairingObservation.lean)
- [Exact proof receipt](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/35a8f86b5f0e555eab25d003353c0c8772578db5/research/owner-observations/verification/RESULT.json)
- [Prior-work comparison](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/35a8f86b5f0e555eab25d003353c0c8772578db5/research/owner-observations/PRIOR-WORK.md)
- [Base constrained construction](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/4ab00a2932f3efdb7091c9a526af4bcd25cc8cd2/research/genome-pedigree/README.md)
- [Alexander specieslike-cluster source](https://arxiv.org/html/2602.05274v1)
- [Related open-questions agenda; model adequacy](https://doi.org/10.1098/rsos.261059)

### Exact sampled-family recovery from independent binary inheritance blocks

**Why this is useful.** The estimator is computed from shared observed symbols, and its finite-sample success probability is exact. The proof connects that observable graph to a complete count of disconnection configurations. The repeated-block counterexample shows why counting more blocks is insufficient unless their joint law supplies new information. The calculation is an elementary specialization, not a claim to replace the source reconstruction theory.

**Precise question.** In a one-generation specialization motivated by Kim, Mossel, Ramnarayan and Turner's pedigree-reconstruction work, children belong to disjoint parental pairs, parental symbols at each block are all distinct, and every child copies either parent independently and fairly across children and blocks. Join sampled children when they share a symbol at any of B>=1 observed blocks, then take connected components. What is the exact probability that this observed graph recovers all sampled families, and is independence essential to the gain from additional blocks?

**Result and boundaries.** Contribution: a closed finite-sample success formula for a directly observable connected-component estimator, together with an exact demonstration of why more blocks help only under the stated independence law. The proof connects graph connectivity, a complete count of failure configurations and the pushed observed-data distribution. 

For nonempty sampled family sizes m_i, exact recovery has probability $\prod_i[1-(2^{m_i-1}-1)2^{-B(m_i-1)}]$. Cross-family sharing is impossible under the distinct-parental-symbol assumption. A within-family graph is disconnected exactly when its inheritance vectors occupy a complementary pair with both vectors present; a finite bijection counts this event. For three siblings and two blocks, this estimator succeeds with probability 13/16, compared with 7/16 for the restricted all-three-sharing rule. Adding blocks cannot spoil recovery in this model, but the probability improvement requires independence. Repeating each child's same parental choice across all blocks preserves every block's full fair-copying marginal while three-sibling success remains 1/4. The result concerns the actual observed-symbol connected-component relation, not hidden labels supplied to the estimator.

It does not prove REC-GEN, statistical optimality, a coupling to Wong's recombination law, or Alexander's infinite specieslike classification. It is a restricted exact-recovery deduction; prior reconstruction theory remains credited.

**Proof evidence.** Lean 4.33.1 exact-clean-commit audit at ae0beee8d04e32c45f28d2f465b924d6816c82a5: seven project modules and 31 selected declarations covering graph recovery, probability, observed-output law and dependence counterexample. Saved evidence at checkpoint 35a8f86b5f0e555eab25d003353c0c8772578db5 passed its integrity verifier on 29 September 2026, including source/log hashes, 49 artifact hashes and all selected reports. Allowed axioms are propext, Classical.choice and Quot.sound. This is local compiler evidence plus a fresh integrity check, not a fresh hosted replay. The general finite proof is distinct from the supporting exact enumerations. The packet makes no worldwide novelty or first-formalization claim and does not claim a formal proof of the full source theorem.

**Primary result:** [Read the full mathematical note](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/35a8f86b5f0e555eab25d003353c0c8772578db5/research/pedigree-block/README.md).

- [Source pedigree reconstruction paper](https://arxiv.org/abs/2005.03810)
- [Recovery and observed-output theorem](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/35a8f86b5f0e555eab25d003353c0c8772578db5/real/PedigreeBlockRecovery.lean)
- [Independence counterexample](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/35a8f86b5f0e555eab25d003353c0c8772578db5/real/PedigreeBlockDependence.lean)
- [Exact local proof receipt](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/35a8f86b5f0e555eab25d003353c0c8772578db5/research/pedigree-block/verification/RESULT.json)
- [Source correspondence and limits](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/35a8f86b5f0e555eab25d003353c0c8772578db5/research/pedigree-block/source/PRIOR-FORMALIZATION-CHECK.md)
- [Related calibration agenda; not the source of this exact theorem](https://doi.org/10.1098/rsos.261059)

### Current player membership does not determine a predecessor-restoring split

**Why this is useful.** This small witness is a practical state-design test: an implementation that must restore immediate predecessors has to retain enough predecessor information. Its strength is the explicit source connection and legal-operation check. The binary-tree ambiguity and quotient criterion do not warrant an inflated claim of mathematical novelty.

**Precise question.** Abramsky et al., Open Questions about Time and Self-reference in Living Systems, section 6.4.3, ask how to model games whose actions merge or split the decision makers. For the precise predecessor-restoring operation motivated by the IPDm implementation, is the unordered partition of persistent sites into current players sufficient to determine the result of every admissible split of the same designated composite? This is one structural subproblem formulated by the project, not the complete changing-player game question.

**Result and boundaries.** Contribution: a concrete failure test for a proposed state description in games with changing players. The checked witness holds the chosen current composite fixed, uses legal merge histories and admissible splits, and locates the missing information in predecessor structure. 

No. Start with four separate sites. Merging 0 with 1 and then with 2, or merging 1 with 2 and then with 0, produces the same current partition {{0,1,2},{3}}. The same composite then splits into {{0,1},{2},{3}} or {{0},{1,2},{3}} when its immediate predecessors are restored. Lean proves legal adjacent-merge histories, equal unordered current partitions, admissible splits with the same designated group and spectator, unequal resulting partitions, and absence of any exact partition-only deterministic split even when correctness is required only on admissible states. A separate test of pinned IPDm operators reproduces the collision with declared constructor/NumPy mocks.

The general factorization criterion is established mathematics. This is a source-motivated structural application, with no broad novelty claim. It neither proves a full implementation refinement nor supplies controller/payoff/equilibrium semantics, and it does not exclude stochastic reduced models under additional distributional assumptions. The authors' full changing-player question remains open.

**Proof evidence.** Lean 4.33.1: eight selected MergeHistoryProjection endpoints, plus eight reused ExactAbstraction endpoints in the original combined receipt. The later predictive-memory proof replay includes those same 16 historical endpoints among 108 reports over 37 project sources. Hosted run 36295740474 succeeded at the submitted source head da67b295530e175c8015a2151f30827ae2a5ad01; its Verify workflow also succeeded. Pinned source hashes match the saved receipt. Allowed axioms are propext, Classical.choice and Quot.sound; no sorryAx or custom axioms. The source-level IPDm operator test is separate evidence and is not certified by the Lean model. Project agent review is internal, not independent expert review. Requested status is a Partial result on the explicit structural subproblem, with statement fidelity and eligibility still open to external review.

**Primary result:** [Read the full mathematical note](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/da67b295530e175c8015a2151f30827ae2a5ad01/research/open-problems/time-self-reference/exact-abstraction/MERGE-HISTORY.md).

- [Published open-questions paper, section 6.4.3](https://doi.org/10.1098/rsos.261059)
- [Accessible source-paper preprint](https://arxiv.org/abs/2508.11423)
- [Admissible-split obstruction in Lean](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/da67b295530e175c8015a2151f30827ae2a5ad01/research/open-problems/time-self-reference/exact-abstraction/MergeHistoryProjection.lean)
- [Pinned source implementation](https://github.com/lksshw/IPDm/tree/eca9b122480b8c654081d6a844176417aefbbcae)
- [Successful proof replay including historical endpoints](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/actions/runs/36295740474)
- [Source-to-result map and remaining questions](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/da67b295530e175c8015a2151f30827ae2a5ad01/research/open-problems/time-self-reference/PROOF-STRUCTURE.md)

## The Thue–Morse update

The [existing VibeMathed entry](https://vibemathed.com/problem/exact-thue-morse-matching-heights-in-an-avoiding-population) concerns the actual attained maximum matching length at every start in the specified avoidance graph. It includes the sharp coefficient 8/3, equality cases and a certified digit evaluator. Its original reviewed snapshot is `19544a4d7608c8cc0d5a1205605c0f38631ca05f`; that record is preserved.

The discussion now points to a checked continuation. If an edited sequence agrees with Thue–Morse from index m onward, construct its corresponding edited avoidance graph and write L_s(v) for its actual matching maximum. Its least integer additive allowance is

```math
B_s=\max_{1\le v\le 3\cdot2^{m+3}+m}(3L_s(v)-8v),\qquad -1\le B_s\le8m-1.
```

The maximum is attained and controls every positive start. This is an exact terminating finite algorithm; no efficient runtime or optimal cutoff is claimed. The graph depends on the edited sequence, so this is not silently changing the target while keeping the original graph fixed. The [individual optimum proof](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/a2644182b147eb40816abb278e00c3c6d4709eb8/notes/REFINEMENT-INDIVIDUAL-FINITE-EDIT.md) and [phase maximum proof](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/a2644182b147eb40816abb278e00c3c6d4709eb8/notes/PHASE-HEIGHT-FORMALIZATION.md) are pinned to the [successful hosted checkpoint](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/actions/runs/36173386580).

## Other completed work that remains part of the public record

These results belong in a comprehensive portfolio even when a new-discovery catalogue is not the appropriate separate outlet for each one.

### Exact predictive state, memory and stochastic observations

The [reading route](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/da67b295530e175c8015a2151f30827ae2a5ad01/TIME-AND-MEMORY.md) and [precise results](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/da67b295530e175c8015a2151f30827ae2a5ad01/research/open-problems/time-self-reference/predictive-memory/RESULTS.md) explain the coarsest exact deterministic output-preserving state, unique factorization from any attained exact representation, intervention restriction, conditional feedback preservation and a global finite-depth stabilization certificate. The parity/history model has four necessary attained predictive states, while no fixed recent suffix determines arbitrary-record parity. Changing the allowed probe can change what memory is necessary.

The [stochastic continuation](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/da67b295530e175c8015a2151f30827ae2a5ad01/research/open-problems/time-self-reference/predictive-memory/STOCHASTIC.md) proves the discrete PMF lumpability criterion, uniqueness and complete finite joint observation/action-law preservation under explicit initial-law and controller conditions. Matching separate marginals is insufficient. An all-horizon six-state example also shows that equal complete output-trace laws need not yield an exact commuting state kernel on the predictive profiles.

These are established behavioral-equivalence, minimization, lumpability and trace/bisimulation ideas, formalized with explicit source and model contracts. The package adds a checked implementation and applications, not a claim to have originated those theories. Hosted proof replay [36295740474](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/actions/runs/36295740474) succeeded at `da67b295530e175c8015a2151f30827ae2a5ad01`; its 108 selected reports across 37 project sources include historical results and supporting lemmas. They are not 108 new biological discoveries.

The separate impossible-versus-rare calibration result remains a written proof with exact finite checks: for n independent trials and known branch probability e, let q=(1-e)^n. The optimal sum of the two errors is q, while the optimal worst error is q/(1+q). Its general probability theorem is not labeled Lean-checked. The [source map](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/da67b295530e175c8015a2151f30827ae2a5ad01/research/open-problems/time-self-reference/PROOF-STRUCTURE.md) records the proof and the unformalized gate.

### Marked ARG construction and conditional pedigree transfer

The [checked marked-process checkpoint](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/35a8f86b5f0e555eab25d003353c0c8772578db5/research/wong/continuation-2026-09-27/CHECKPOINT.md) makes source-model mathematics publicly inspectable. It includes the evolving lineage recorder, conditional continuous breakpoint law, measurable dated-history output, almost-sure validity and absorption, and explicit owner-map assumptions for transferring ancestry statements. The selected-declaration closure was checked locally at proof commit `1ac3dd9446e7264336f0764040ff47ad684099cb`: 77 project modules and 415 selected reports, including 317 prior reports and 98 additions.

The reader should distinguish the source construction from the project's bridge theorems. Preserving individual edges does not by itself lift every ancestry path. The owner-map theorems state the additional hypotheses, with counterexamples when they are dropped. Finite ancestry disagreements per representative have a separately checked IAP invariance statement. These are mathematical transfer contracts, not evidence that a real species classifier has been validated.

The [Wong source paper](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/) remains credited. The Little-ARG equality-in-law target, expected-event asymptotics, general serialization/conformance and empirical claims retain separate open obligations. Almost-sure finite event count alone is not a finite-expectation result.

### Word, graph and cellular-automaton extensions

The [ten-proposal result inventory](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/a2644182b147eb40816abb278e00c3c6d4709eb8/TEN-SOLUTIONS.md) contains the proof routes and source audits. Its exact main results are:

| Result family | Proven scope and attribution boundary |
|---|---|
| Fixed-source-gender threshold | Cap two is attainable through a directed line-graph construction while retaining whole-graph inspecies; smaller caps are impossible. The line-graph method is classical. |
| Minimum crossing width | At the stated minimum eventual width, rigidity identifies the kth power of a ray for every finite k. |
| Fair finite port encoding | Exact encoding of the declared critical populations; an eventually periodic complete schedule realizes every infinite word. Finite-state methods have established precedents. |
| Matching maxima | Exact all-start Thue–Morse heights, the phase algorithm and finite-edit optimum described above. |
| Quantitative avoidance | A period/antiperiod break modulus gives an explicit iterated-clock bound; aperiodicity alone permits arbitrarily slow finite avoidance. |
| Productive pruning | Preserves the full infinite word language and stated eligibility/cap conditions; maximality variants have separate conclusions and counterexamples. |
| Boundary repair | Finite parent-label deficiency exactly characterizes deletion-only eligibility repair on a fixed infinite retained set; the canonical repair maximizes edges and minimizes roots. |
| Stateful cellular automaton | A specified synthetic three-state rule has static east support optimum one, while a state potential excludes every nonzero horizontal finite-support spaceship. This is not a claim about a natural binary or published CA rule. |

The separate [ordinal and embedding question ledger](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/a2644182b147eb40816abb278e00c3c6d4709eb8/QUESTION-LEDGER.md) records prior certificates, obstructions and residual questions. Further research is proceeding in its own coordinated lane. Results from that lane enter this guide only after their exact public checkpoint and evidence are available; an in-progress report is not a publication receipt.

## Evidence, attribution and reproducibility

- Proof claims are tied to exact Git objects, theorem names and receipts. Later documentation publication does not change the pinned proof inputs.
- Local receipt integrity checks compare committed sources, compiler logs and artifact hashes. They are distinct from rerunning the compiler or obtaining a new hosted build.
- The allowed reported Lean axioms are `propext`, `Classical.choice` and `Quot.sound`. This audits admitted formal proofs; it does not certify biological applicability, original problem correspondence or worldwide priority.
- Reviews by other agents in the same project are internal reviews. They are not independent human expert endorsement. Author names identify cited sources, not collaborators or endorsers of these submissions.
- The human collaborator selected directions and requested source correspondence, intelligible exposition, checks and publication. Codex agents developed the project's constructions, deductions, Lean proofs and explanations. AI use is disclosed in each submission.
- Novelty is scoped to the stated candidate incremental construction or deduction. Known quotient theory, finite epigenetic models, pedigree ambiguity and reconstruction theory remain credited.

The source release is the explicitly approved frozen checkpoint [`35a8f86b5f0e555eab25d003353c0c8772578db5`](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/tree/35a8f86b5f0e555eab25d003353c0c8772578db5), published on `codex/biology-observations-vibemathed-2026-09-29`. The other proof packages retain their own pinned commits above. Public source availability, catalogue inclusion, independent review and journal publication are different states.
