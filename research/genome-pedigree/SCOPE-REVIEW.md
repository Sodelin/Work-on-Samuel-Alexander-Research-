# Independent scope and statement review

Reviewed branch: `codex/genome-owner-bridge-2026-09-27`.
This is a bounded source and mathematical-communication review of
`GENOMES-AND-PEDIGREES.md`, this packet's `README.md`, and the three Lean
modules listed below. No Lean process was run by this reviewer. Only this
review file was written. The replay receipt remains the authority for
compiler and axiom-check status.

**Scope verdict: pass, with two wording defects and one implementation-scope
clarification resolved during review.**
The actual theorem statements support the constrained deterministic
counterexample. I found no remaining material mismatch between their
hypotheses and the central public claim. This is not an independent compiler
receipt, nor a broader biological or novelty endorsement.

## Concrete findings and disposition

| Finding | Evidence and required meaning | Disposition |
|---|---|---|
| The initial public table assigned two parents to every organism. | `PairingCore.TwoParents` only covers positive generations; `founders_exactly_four` proves precisely four parentless founders. | **Resolved:** the public table now says two distinct parents per nonfounder, with two children per organism. |
| “Any prescribed finite prefix” could mean any prescribed ownership values. | `constrained_counterexample N` selects `S = 2*(N+1)` and agrees with the one fixed `mixing` schedule through N. It does not extend every possible prefix with both outcomes. | **Resolved:** the public table says ownership through any prescribed finite generation; README explicitly distinguishes arbitrary length from arbitrary prefix contents. |
| The finite coordinate implementation should be legible. | `PairingGARG.fullInterval` uses `Nat` coordinates and `[0,1)`. `atLocus_iff` states that the only covered locus is 0. No nucleotide strings or sequence likelihoods occur. | **Resolved:** the technical README now identifies the single unrecombined abstract region, locus 0, and omitted sequence-level data. It defines completeness as retention of all vertices and realized transmissions in the declared model. |

## Statement-to-meaning checks

| Claim checked | Source evidence and assessment |
|---|---|
| Complete common realized transmission history | `PairingCore.Genome` is the same relation on all natural-number encoded copies for both schedules, not merely agreement on a sampled subgraph. It contains exactly consecutive-generation same-lane edges. No owner field enters this graph. **Pass.** |
| Exactly two contemporaneous copies per organism | `owner_copy` preserves the generation by construction; `owner_exactly_two` quantifies over every organism and characterizes its entire fibre with two distinct copies. This excludes vacant owners and hidden extra copies. **Pass.** |
| Exact pedigree edges and nonselfing degree controls | `edge_exact_image` is a biconditional. `two_parents` and `two_children` characterize all neighbors, while the instantiated schedules prove the `Allowed` hypotheses. `parents_opposite_sex` and `same_copy_sex` supply a consistent binary parent-sex control without distinguishing the observations. These are concrete combinatorial conditions; they are not a full meiosis or sex-chromosome model. **Pass.** |
| Infinite mixing conclusion | `mixing_late` proves reachability to every organism at every generation at least three steps later. `mixing_cofinite` turns that bound into finite non-descendants. The all-time conclusion is not extrapolated from a simulation. **Pass.** |
| Genuine opposite IAP | The splitting result chooses a tail organism with infinitely many descendants and infinitely many non-descendants, then contradicts the existing IAP definition. Early weak connectivity is proved separately. Thus failure of IAP is not being confused with disconnectedness. **Pass.** |
| Specieslike and inspecies claims | `mixing_maximal`, `splitting_not_specieslike`, `mixing_inspecies` and `splitting_not_inspecies` explicitly prove the advertised whole-population statuses using existing definitions. Whole-population maximality uses its being the entire ambient population. Neither the sources nor the prose infer a classification or count of empirical species or of all proper clusters. **Pass.** |
| Arbitrary finite observation length | `no_iap_decoder N` ranges over every function of the fixed graph and `observedOwners N`, including noncomputable predicates. The counterexample belongs to its explicitly defined `Family`. The shared dates, interval annotations and per-copy sex labels cannot distinguish the pair either. This is a failure of a universal decoder on that family, not failure for every particular ownership record. **Pass with the corrected wording.** |
| Finite Wong representation | `finiteARG T` really has a finite node type. `finite_topology_iff_genome` preserves and reflects edges under an injective code; `finite_pedigree_exact_image` has the necessary endpoint-generation bounds. `extraction_retains_every_edge` applies at locus 0 with all terminal copies sampled. The owner map is supplied additional data. **Pass.** |
| Dates and source assumptions | `generation_dated_biosphere` chooses the actual real-valued generation as birthdate and supplies strict parent-before-child times, finite real-date sublevels, finite child sets and an infinite population. This has no upper lifetime or demographic probability assertion. **Pass at source-statement level; replay remains separate.** |
| Failure of path lifting | `exact_edges_do_not_lift_paths` proves an organism path from 0 to 9 and excludes every genomic path between any representatives of their owner fibres. The intermediate edges use different lanes. The prose correctly identifies the missing ancestry-reflection condition, despite exact edge preservation. **Pass.** |

The infinite/finite distinction is essential and is preserved in the reviewed
text. A finite gARG truncation does not itself carry the opposite infinite-
population IAP conclusions: on a finite candidate population, finite
descendants make IAP automatic. The finite interface certifies that every
prefix is a legitimate representation with exact edges; the infinite
`PairingCore` arguments establish the contrasting limits. Sampling all terminal
copies in that interface does not silently supply their organism ownership.

The biological wording is appropriately conditional. “Segregation-compatible”
describes the displayed copy contributions and nonselfing parent assignment;
the README immediately permits consanguineous mating and withholds a full
recombination/sex-chromosome probability model. Both pages distinguish the
mathematical construction from a fitted prediction and an experimentally
supported mechanism. Neither equal likelihood nor positive probability of
the prescribed infinite history is claimed.

The source comparison retains the necessary Thatte/Wong distinction: the
former pairing rule sees both potential homologues; the latter realized
interval graph need not contain the unused potential predecessor. The
reviewed wording neither contradicts Thatte's richer observation model nor
asserts priority for generic pedigree non-identifiability. The potential
contribution stays at the conjunction of constraints and the IAP application.
The separate Royal Society track is not declared complete at the level of
its authors' full questions.

## Reviewed snapshot and remaining gate

SHA-256 values at the statement-review checkpoint:

| File | SHA-256 |
|---|---|
| `GENOMES-AND-PEDIGREES.md` | `a933a57a15615731b80ed7e98306bb54136325f3479b15ef40ba7056406bf098` |
| `research/genome-pedigree/README.md` | `d1918a8e332ad3d3b8b15e3433427cf4814c60997df703b46234157ffba39c9f` |
| `research/genome-pedigree/PairingCore.lean` | `f8723988f843354641a66e7cb71b021721864132d9f46b269efab2697c66db94` |
| `research/genome-pedigree/PairingGARG.lean` | `1dc127444928e95eb19945b31087a79125567097a41d664f5c708b89bde40b15` |
| `research/genome-pedigree/PairingBridge.lean` | `7137a1a7ab729bb395fb1e73a56c2fcfdcc94e3cc3fb4a7119bf8ec09597d40c` |

The implementation lane reported a final bridge proof repair and planned
fresh replay when requesting this review. This reviewer has inspected the
resulting source, not independently executed it. Release statements about
compilation must follow a successful fresh receipt matching the final source
hashes. A source-scope pass does not waive that gate.
