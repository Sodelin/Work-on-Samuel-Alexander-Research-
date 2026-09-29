# Independent audit of the ordinal characterization

Audit date: 29 September 2026. Scope: source and proof reading, mathematical checking, and a precise follow-on proposal. The audit did not rebuild the complete repository, modify either research checkout, install anything, publish, contact an author, or change task visibility. A new isolated bridge was subsequently compiled successfully; its fresh evidence is recorded at the end of this document. Historical successful compilation receipts for other modules remain prior execution evidence.

The principal finding is positive: the existing generic reachable-state ordinal equivalence is a genuine, correctly formulated theorem. The natural-valued strengthening is also genuine and proves leastness and attainment. The inspected proofs do not assume an external continuation bound or conceal the conclusion in a population adapter. The actual history-tree omega calculation is correct but has a narrower Lean interface than the generic certificate theorem. These results answer a precise literal reading of the source question; they do not establish a new structural hierarchy of avoiding genealogies or historical novelty.

## The source question and a defensible interpretation

Alexander asks for a characterization of the populations realizing a fixed possibly avoidable sequence, with special interest in ordinals and the analogy with Schmidt's rayless-graph rank. The wording does not specify a rank, spectrum, algorithm, or reconstruction theorem. The relevant source is [Alexander, Section 6](https://arxiv.org/html/1212.0186v2#S6), rechecked directly on 29 September 2026.

Accordingly, an exact equivalence between nonrealization and existence of an ordinal certificate is a legitimate answer to a precise interpretation of that request. By complementation it also characterizes realization. The stronger claim that this is the intended structural resolution does not follow from the source wording or from Lean. This is especially relevant because the equivalence comes from the standard ordinal rank of a well-founded relation and holds far beyond the population class.

Suggested claim: “For a prescribed sequence, we give an exact reachable-state ordinal characterization, prove its finite-valued form under the population's local finiteness, and identify the collapse of the ordinary matching-history rank.” Avoid: “We have established a new transfinite structural classification of all avoiding populations.”

## Definitions and proof audit

All source paths in the following table are under:

`C:/Users/Owner/Documents/Codex/2026-09-27/wong-alexander/research/open-questions/ordinal/`

| Source and principal endpoint | What it actually proves | Audit finding |
| --- | --- | --- |
| `GenericCertificate.lean:124`, `realizes_iff_state_chain` | An actual target realization is equivalent to an infinite forward chain of reachable vertex/phase states. | Correct. The reverse direction allows its chain to start at any reachable phase, not just zero, and explicitly splices a witnessing finite prefix to the chain. |
| `GenericCertificate.lean:161`, `avoids_iff_wellFounded` | Avoidance is equivalent to well-foundedness of the relation with child as first argument. | Correct relation orientation. Uses the standard no-descending-chain characterization with classical choice. |
| `GenericOrdinalCertificate.lean:43`, `avoids_iff_ordinal_certificate` | For arbitrary vertex and label types, avoidance iff an ordinal decreases on each reachable transition. | Correct. No finite-branching, birth-date, finite-root, countability, or alphabet-finiteness premise. Forward certificate is actual `Acc.rank`; converse pulls back the well-founded ordinal order. |
| `GenericCertificate.lean:216`, `avoids_iff_natural_certificate` | The same equivalence with natural values when each fixed vertex and label has finitely many children. | Correct. Finiteness of the alphabet is not required. The injection from state-successors to graph-successors uses the forced next phase. |
| `GenericCertificate.lean:228`, `avoids_has_least_attained_certificate` | A pointwise least natural certificate exists, its value is an attained continuation-chain length, and it bounds every continuation-chain length. | Correct. `finiteHeight` is well-founded recursion using a finite supremum; the proof of attainment separately handles the zero-successor case. |
| `HistoryConverse.lean:27`, `below_wellFounded_iff_avoids` | Equivalence for the actual finite-history tree of a `BinaryNatPopulation`. | Correct. Histories retain the whole path, and their paths stabilize after the endpoint. They are not merely endpoint/phase pairs. |
| `OrdinalHistoryRank.lean:70,78`, `history_rank_eq_height`, `root_rank_eq_omega` | Every nonroot history has its exact attained natural continuation height; the artificial root has Mathlib ordinal rank omega. | Correct. The lower bound is derived from the population axioms, not supplied as an external cofinality premise. |
| `HistoryPruning.lean:57,74`, `omega_stage_iff_root`, `omega_succ_stage_empty` | For an avoiding binary natural-date population, the first-limit derivative is exactly the artificial root, and the following derivative is empty. | Correct concrete first-limit calculation. It is not a general transfinite derivative implementation. |
| `OrdinalCertificates.lean:72,79`, `odd_ray_realizes_tail`, `no_all_phase_natural_rank` | The graph P_s always realizes the tail beginning at phase one, and hence cannot admit an all-phase natural certificate. | Correct. This standalone copied-definition file does not itself prove avoidance of s; that premise comes from the existing classification construction. The all-phase ordinal impossibility is a valid written consequence but has no separate endpoint here. |

### Why the reachable-state restriction is exact

Write R_s for the pairs (v,k) reached by some finite matching prefix of k edges beginning at phase zero. Every (v,0) belongs to R_s. A forward transition is

    (v,k) -> (w,k+1)  iff  E(v,w,s(k)).

The type `State E s` is the subtype of these reachable pairs. In the reverse direction of `realizes_iff_state_chain`, the chain may begin at phase k>0. Its proof recovers a prefix p ending at the first chain vertex, sets q(n)=p(n) for n<k, and q(n)=f(n-k).vertex thereafter. It checks the boundary edge n+1=k separately. This is the necessary concatenation step, and it is present in the code.

By contrast, the unrestricted phase graph V x N includes tails that no matching prefix can reach. In the displayed binary construction, 1,3,5,... has labels s(1),s(2),s(3),.... For an s that is not eventually periodic, P_s avoids s by the prior classification proof, while the unrestricted phase graph still contains

    (1,1) -> (3,2) -> (5,3) -> ... .

The initial state is unreachable because 1 is a root; all later displayed states are unreachable as well, since a reaching prefix would combine with the remaining ray to realize s. An ordinal decrease along this unrestricted ray is impossible. Replacing R_s by all of V x N is therefore a mathematical error, including for bounded-degree populations.

### Why the generic predicates fit the source model

Alexander's realization is a vertex sequence with successive directed edges carrying the successive target labels. `GenericCertificate.Realizes` expresses exactly that relation. The generic theorem permits more graphs, including graphs without unique edge labels or chronological ordering; the source model is a subclass. Chronology prevents repeated vertices in a source-model realizing path, so the generic allowance of a vertex sequence creates no mismatch there. The label universe does not restrict the vertex universe or require an enumeration.

A faithful translation of a concrete population's edges is still necessary for an application. Generic quantification does not validate an incorrectly encoded edge relation. However, no nontrivial binary coding or real-to-natural reindexing is needed to use the generic certificate theorem directly on the original vertex and label types.

## The history rank and its limits

`HistoryWellFounded.History` is a finite matching history represented by a length and an eventually constant path function. `Child` appends exactly one matching edge. `Node` adds an artificial root, whose children are exactly the zero-edge histories, one for each start vertex.

The proof of finite nonroot ranks reduces to the least continuation rank on the reachable endpoint and phase. The proof that the root is not merely bounded by omega is population-specific: `HistoryWellFounded.finite_word_occurs` invokes `PositiveUnavoidability.backward_word`, which derives finite-word occurrence from the existing population conditions. Thus finite matching lengths across starts are unbounded, even though each individual start has finite maximum under avoidance. The root rank is therefore sup_v(h(v)+1)=omega.

The source-general written argument is sound: finitely many roots and finite total child sets make each finite root neighborhood finite. Choose a terminal vertex outside the neighborhood of depth m-1 and pull back a prescribed m-letter word using the incoming-label condition. Encountering a root too soon would contradict that choice. Source chronology supplies the usual genealogical interpretation; it is stronger than necessary for this finite-word argument.

The Lean root-rank and history-pruning modules inspected here nevertheless use `Nat` vertices, `Bool` labels, and `BinaryNatPopulation`. Their generic certificate companions do not automatically broaden those separate endpoints. Under generic finite per-label branching alone, the root rank can be a finite ordinal. To force equality with omega one also needs unbounded matching-prefix lengths; the source population axioms supply it.

The written Schmidt calculation is also correct. The rank definition assigns zero exactly to finite graphs and proceeds by finite deletion into lower-rank components. This is the definition in [Bonato, Bruhn, Diestel and Spruessel, Definition 2](https://www.uni-ulm.de/fileadmin/website_uni_ulm/mawi.inst.081/Henning/raylesstwins.pdf), which attributes the construction to Schmidt. For an avoiding source population, deleting the artificial root of the history tree leaves the finite matching trees T_v. The whole history tree is infinite, so its Schmidt rank is exactly one. Every finite deleting set that leaves the artificial root also leaves infinitely many of its singleton-history children in one component. Consequently its Schmidt kernel is exactly that artificial root. These are written deductions; the inspected modules contain no Schmidt-rank implementation.

Neither omega nor Schmidt rank one distinguishes different avoiding populations. The kernel is a vertex added by the encoding and is not a genealogical separator in the original population. A richer structural classification remains an additional problem and needs a specified recursive operation before there is a meaningful ordinal-spectrum conjecture.

## A crucial distinction for the new pruning theorem

For the reachable-state graph, every state has finitely many matching successors. Let

    S_0 = R_s,
    S_(n+1) = {x : some successor of x belongs to S_n},
    C = intersection_n S_n.

Finite branching makes C a fixed point for every graph: a state has arbitrarily long finite continuations iff some child has arbitrarily long finite continuations. The converse-to-child direction follows by taking a maximum of the finitely many child failure bounds. Classical choice then builds an infinite continuation inside C. Hence C is the greatest set whose every member has a successor in the set. Avoidance is equivalent to C being empty.

This is different from the artificial-root history tree. That root has infinitely many children, even though each other history has only finitely many. In an avoider, its finite-stage survival is supported by ever-changing start vertices; it survives at omega and disappears at omega+1. Consequently:

- Reachable-state pruning under avoidance: S_omega is empty.
- Artificial-root history pruning under source-model avoidance: D_omega is {root}, and D_(omega+1) is empty.
- Artificial-root history pruning for a realizing population: D_omega contains the infinite matching histories and is already fixed.

Conflating the first two objects would invalidate a stage claim. The parent implementation lane has been notified of this distinction.

## Precise useful next theorem: canonical finite-height/live-core decomposition

This is a proposal with a written proof, not an additional checked endpoint in this audit. It builds directly on the parent's planned greatest-fixed-point formalization.

Let X be an arbitrary state type with a successor relation and finitely many successors at each state. No global avoidance premise is imposed. Let C be the greatest successor-closed-in-the-existential-sense set described above. Then:

1. X is partitioned into C, the states admitting an infinite forward continuation, and M=X\C, the states with bounded finite continuation lengths.
2. M is closed under every forward successor: an edge from a state in M to C would supply an infinite continuation from that state.
3. Each x in M has a uniquely determined attained maximum h(x) in N. It satisfies h(x)=max({0} union {1+h(y): x->y}), and is the pointwise least decreasing natural certificate on M.
4. Defining H(x)=h(x) for x in M and H(x)=infinity for x in C produces the unique function X -> N union {infinity} satisfying the Bellman equation

       H(x) = sup({0} union {1+H(y): x->y}).

5. For each finite n, x survives n pruning rounds iff n<=H(x). Thus the finite elimination layer of a mortal state is exactly h(x)+1, while live states survive every round.

Proof. The finite-successor compactness argument proves (1). Prefixing an edge proves (2). On M, the restricted successor relation is well founded, and `GenericCertificate.finiteHeight` with its existing decrease, leastness, and attainment lemmas proves (3). Infinite continuations force every solution of the Bellman equation to have value infinity along their initial states. On a mortal state, induction on its finite maximum proves that any Bellman solution has exactly that maximum, proving (4). A finite-stage induction proves (5).

A slightly stronger observation is available: define H directly as the supremum of all finite continuation lengths. Its extended-natural Bellman characterization and uniqueness do not need finite branching. Finite branching is needed specifically for H(x)=infinity iff x has an infinite continuation; without it, a root with finite chains of every length but no ray has H=infinity. Keeping this hypothesis boundary explicit would make the generic result useful beyond populations without misidentifying the live core.

This theorem provides information for mixed realizing populations, where some reachable states lead to infinite matches and others die after finite time. The current global-avoidance certificate theorem has no ordinal certificate on that entire state space, so the decomposition is a substantive formal interface improvement. Its method remains classical, and no new general rank method is claimed.

## A bridge to the universal-embedding question

There is also a short, exact transport theorem connecting both research lanes.

Let Q be the positive finite-fibre blow-up of P already used in `GenericUniversalAvoiders.lean`: each v is replaced by nonempty finite copies (v,a), and every original edge is replaced by all edges between its two fibres with the original label. Let pi(v,a)=v. For every target s, phase k, copy (v,a), and finite length m:

- ((v,a),k) is reachable in Q iff (v,k) is reachable in P.
- A tail match of length m starting at ((v,a),k) exists in Q iff one starting at (v,k) exists in P.
- An infinite tail exists from the former iff it exists from the latter.

Proof. Projection maps every relevant finite or infinite path to one in P. Conversely, lift a base path by choosing copy zero at intermediate vertices, using the prescribed copy at the start or endpoint as appropriate. All consecutive lifted vertices remain adjacent because the replacement is complete between fibres. The zero-length case is immediate.

Therefore the exact finite continuation rank, extended height, and live-core membership pull back unchanged along pi. In particular, for an avoider,

    h_Q((v,a),k) = h_P(v,k).

This statement is stronger than equality of the entire realized infinite-word language, because it preserves local continuation information at every corresponding state. It explains a limit of these rank invariants: the blow-ups that defeat countable embedding families can preserve all these pointwise continuation heights. The embedding obstruction uses fibre size and local ball capacity, information that this height profile does not record. The finite-chain and natural-rank part of this bridge is now checked in the isolated module described below. It is not a proposed solution of an unspecified new structural-rank question.

## Verification boundaries and exact file identities

Freshly checked in this audit: actual source text, proof structure, definitions, theorem signatures, phase concatenation, finite maximum construction, finite-word dependency, the odd-tail counterexample, source wording, and the mathematical follow-on proofs. The new isolated bridge additionally passed a direct Lean compilation and axiom audit. No semantic error was found in the inspected endpoints.

Not freshly checked here: a complete repository rebuild, hosted CI, current publication status, worldwide priority, or author endorsement. The historical receipts remain prior evidence for their modules. The new bridge has fresh transitive endpoint axiom reports containing only `propext`, `Classical.choice`, and `Quot.sound`.

SHA-256 values read on 29 September 2026:

| File | SHA-256 |
| --- | --- |
| `GenericCertificate.lean` | `F3B1FBFB72D2E7E08B94FF88279432B809747321E0003EE687C04F6307ED5581` |
| `GenericOrdinalCertificate.lean` | `17C0FBBDD5F904AAFD85BCA42EC0E8836D03A38EBC5389BB6207ABD9A8079510` |
| `HistoryWellFounded.lean` | `E3EFCE200EAC78DD6EC306B3087F5CD0EC87CF8E3F0DB939284C62553133CE96` |
| `OrdinalHistoryRank.lean` | `67B018434E820175AFF7AF2D9FA615D7CD4A42844600380B81259F4925198D74` |
| `HistoryPruning.lean` | `7441B97FD379513DCC4EF852BF3EE8EAE2A2A297EBED2110FE850E2F339E4A3B` |
| `HistoryConverse.lean` | `DA301F530D3F41B7CE7A1D1DC9917011BE7C508B747D252B32C4F62836B09D62` |
| `OrdinalCertificates.lean` | `712CC36D5E75C18F6060439591C392A97AF80F9B3A23A92C70198C4DEAC4D2AF` |

The new audit is deliberately separate from the historical proof sources and receipts. The exact source-general certificate theorem is established in those sources. The source-general explicit history rank, Schmidt implementation, realizing-history fixed point, and a richer structural taxonomy are distinct items; completion of one must not be reported as automatic completion of the others.
## Newly checked bridge module

The source [BlowUpRankInvariance.lean](BlowUpRankInvariance.lean) compiled successfully with the installed Lean 4.33.1 compiler. It imports the same-day rebuilt copies of the frozen `GenericCertificate` and `GenericUniversalAvoiders` modules prepared by the parent and embedding lanes. It defines no replacement population or graph interface. All generated files remain in this audit folder.

Seven endpoints were printed, each with only `propext`, `Classical.choice`, and `Quot.sound`:

1. `BlowUpRankInvariance.reachable_iff` — every individual fibre copy has exactly the original endpoint's phase reachability.
2. `BlowUpRankInvariance.chainLength_iff` — every finite continuation length is preserved and reflected by projection.
3. `BlowUpRankInvariance.naturalCertificate_pullback` — a natural certificate pulls back along projection.
4. `BlowUpRankInvariance.least_attained_certificate_pullback` — an attained base certificate pulls back to an attained, pointwise least certificate on the blow-up.
5. `BlowUpRankInvariance.finiteHeight_eq` — the existing exact `GenericCertificate.finiteHeight` values agree under projection, for arbitrary witnesses of their existence.
6. `BlowUpRankInvariance.population_finiteLabelChildren` — the actual `Population.children` axiom supplies the generic finiteness hypothesis.
7. `BlowUpRankInvariance.avoider_has_exact_rank_transport` — the actual population plus actual avoidance yield a least attained base rank whose pullback is the least attained blow-up rank. There is no external rank, bound, or well-foundedness premise in this final endpoint.

The detailed fresh record is [BlowUpRankInvariance.check.json](BlowUpRankInvariance.check.json), with source and direct-dependency hashes. The raw printed axiom output is [BlowUpRankInvariance.log](BlowUpRankInvariance.log), and [Check-Bridge.ps1](Check-Bridge.ps1) records the exact local driver. This is local kernel verification of the new transport statements, not a hosted or human review claim.
