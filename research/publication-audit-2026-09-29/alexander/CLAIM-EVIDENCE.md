# Alexander directions: claim, source and prior-art audit

Audit date: 29 September 2026. This is a bounded publication audit of three already queued VibeMathed entries. The existing proofs were inspected for statement correspondence; no theorem source was edited, no new proof research was started, and no entry or message was sent. Revision drafts are in [DRAFTS.md](DRAFTS.md); machine-readable fields and character checks are in [VIBEMATHED-REVISIONS.json](VIBEMATHED-REVISIONS.json). Queries, primary sources, access limits and proof hashes are in [SEARCH-EVIDENCE.json](SEARCH-EVIDENCE.json).

**All three directions have explicit source questions. Their claims differ:** the universal-avoider construction gives a negative answer under a specified embedding convention; the founder-window theorem answers the mathematical request to replace common ancestry; the ordinal package gives a precise characterization by applying classical rank and compactness methods, with checked refinements. None of those facts establishes worldwide priority or an independent expert endorsement.

| Direction | Publication verdict | Surviving contribution to lead with |
|---|---|---|
| Universal avoiders | Substantive candidate answer to a specified interpretation of the 2013 question. Retain partial scope for the open-ended source wording. | Nonuniversality persists with exactly one incoming parent of each label; the construction preserves the population axioms, roots and selected full path language, and defeats any countable host family at every finite global edge-stretch bound. |
| Ordinal characterization | Direct answer as an exact criterion; risk of being judged a straightforward application of established theory. Keep attribution explicit. | Reachable states give exact realization, pruning and least attained finite continuation heights, including mixed populations; complete blow-ups preserve those heights despite the embedding obstruction. |
| Real founder window | Particularly direct candidate answer to the mathematical non-CA direction. Retain partial scope for biological plausibility. | Every organism, and more strongly every already admissible cluster, extends into a maximal cluster in one fixed real-duration class that allows multiple founders. |

## 1. Exact source questions and versions

**Alexander (2013), Biologically unavoidable sequences**, Electronic Journal of Combinatorics 20(1), P31, DOI 10.37236/3035. The journal version's Section 6, printed p.12, separately asks about populations that are **“universal among all such”** and **“a characterization in terms of ordinal numbers.”** The model is Definition 1, p.1. The [journal PDF](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v20i1p31/pdf/) is the preferred locator. The [arXiv v2](https://arxiv.org/pdf/1212.0186v2) has different pagination and theorem numbering: Section 6 is p.9, and the eventual-periodicity result is Theorem 6 rather than journal Theorem 10. A regenerated PDF date is not a new publication date.

**Alexander (2026), Specieslike clusters based on identical ancestor points**, Journal of Mathematical Biology 92, article 41, DOI 10.1007/s00285-026-02361-x, published 28 February 2026. In the accepted [arXiv:2602.05274v1 manuscript](https://arxiv.org/pdf/2602.05274v1#page=17), Section 6, p.17, immediately after Theorem 13, the author requests **“a solution not requiring the CA property.”** Informal Question 4 is on p.9; it also asks for biological plausibility. Theorem 13 on p.16 supplies existence with CA and REF. The [publisher record](https://link.springer.com/article/10.1007/s00285-026-02361-x) confirms publication identity and acceptance on 2 February 2026, but its full text was subscription-gated. The live arXiv record listed only v1. Cite the accepted manuscript for exact locators; no line-by-line publisher-PDF comparison is claimed.

The two 2013 questions are separate from the eventual-periodicity classification question. The [published VibeMathed classification entry](https://vibemathed.com/problem/classification-of-biologically-unavoidable-sequences) explicitly excludes ordinal and universal-object questions from its scope. That editorial record disambiguates scope; it is not independent mathematical proof or a novelty certificate for this work.

## 2. Universal avoiders: answer and surviving increment

The discovery is: **even exact incoming-parent counts do not produce a countable catalogue containing all avoiding populations.** The proof preserves genealogy constraints while enlarging finite neighborhoods enough to defeat any proposed catalogue.

### Convention and predecessor comparison

Alexander invokes Cherlin and Shelah without defining an embedding relation. Their [Universal graphs with a forbidden subtree](https://arxiv.org/pdf/math/0512218), Introduction, manuscript p.1 (journal p.293), distinguishes subgraph from induced-subgraph containment and uses the former as its default. Theorem 1, manuscript p.3, classifies finite forbidden trees allowing universal graphs: paths and near-paths. That is not the infinite labelled-path/population problem here.

The relevant obstruction is older. [Lehner, A note on classes of subgraphs of locally finite graphs](https://arxiv.org/pdf/2205.12824), arXiv v1 (25 May 2022; journal 2023), p.2 and Corollary 3.6, p.8, credits de Bruijn through Rado for nonuniversality of connected locally finite graphs. Theorems 1.1 and 3.1 give host criteria. Corollary 3.2 gives a locally finite host for a fixed bounded-degree graph class. Thus general local-finiteness nonuniversality is not newly discovered, and subclass hypotheses matter. Rado's original text was not independently read in this pass; attribution is through Lehner.

A negative theorem for all locally finite graphs does **not** imply a negative theorem for an arbitrary subclass: a subclass may have a universal member. Our extra step stays in the avoidance class while maintaining chronological and parental requirements.

### Exact checked increment

Main source: [TerminalCloneAvoiders.lean](../../open-questions/continuation-2026-09-29/embedding/TerminalCloneAvoiders.lean). Earlier source: [GenericUniversalAvoiders.lean](../../open-questions/embedding/GenericUniversalAvoiders.lean).

1. `no_countable_bounded_stretch_family` starts with any population and a countable family of countable locally finite hosts. It produces a terminal-clone population with root fibres of size one and the same entire infinite-word language. No injective map to any host has a finite global bound on the lengths of edge images.
2. `incomingParentEquiv` gives a bijection of each original incoming-parent set, separately for every label, with the corresponding parent set of each copy. Cloning preserves arbitrary original incoming-parent counts. Noncanonical copies have no children; canonical copies carry the outgoing edges.
3. `avoiding_no_countable_exact_parent_bounded_stretch_population_family` specializes to an avoiding population already having exactly one parent of each label. It preserves that property and its complete language.
4. `avoiding_no_countable_exact_parent_family_from_any_population` selects one parent of each label before cloning. Selection preserves the actual root set and avoidance, but may discard other infinite words. The final language is a subset of the original and equals the selected population's language. This endpoint targets arbitrary countable population-host families, including hosts that realize the target word.
5. `rootsEquiv` and `selectedClone_rootsEquiv` preserve actual root sets, not merely a count inequality.

The obstacle is simultaneous preservation. Multiplying all edges across fibres creates neighborhood growth but changes incoming-parent counts. Terminal cloning changes which copies reproduce, allowing large finite fibres without changing parent sets. Birth sublevels and child sets remain finite, even though their sizes have no shared finite bound.

The countable-family and all-finite-stretch conclusions are stronger statements than failure for one host, but their extension is elementary after the preservation construction. They should not be marketed as a new general diagonal method.

### Scope for the entry

Failure already holds for injective adjacency-preserving maps after directions, labels and chronology are forgotten, hence for usual stronger embeddings. It does not obstruct arbitrary noninjective homomorphisms. There is no fixed global child cap. Terminal individuals are allowed. Arbitrarily unbounded edge stretch is not settled. Do not claim exact original-language equality after arbitrary parent selection, or combine terminal-clone parent preservation with complete-blow-up rank preservation as if these were one construction.

**Significance:** Exact incoming-parent constraints do not rescue universality; neighborhood growth remains compatible with the population axioms.

## 3. Ordinal characterization: exact answer, classical method

The discovery is: **a reachable matching state either supports an infinite continuation or has a longest finite continuation, whose length exactly measures its pruning removal time.** This characterizes realization and quantifies failure at each start and phase.

### Closest established theory

[GenericOrdinalCertificate.lean](../../open-questions/ordinal/GenericOrdinalCertificate.lean) imports `Mathlib.SetTheory.Ordinal.Rank` and applies its rank to matching states. The [official Mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/SetTheory/Ordinal/Rank.html) documents `Acc.rank` and `Acc.rank_lt_of_rel`: the machinery is already general. The fact that a well-founded relation admits a descending ordinal rank is established mathematics.

For older methodological context, Cousot and Cousot's [An Abstract Interpretation Framework for Termination](https://www.di.ens.fr/~cousot/publications.www/CousotCousot-POPL12-ACM-p245-258-2012.pdf), POPL 2012, pp.245–246, formulates termination and infinite-trace semantics using ranking functions and fixed points. This audit does not claim that their formulas by themselves settle Alexander's exact population encoding. Phrase search in the PDF failed for some later text; no uninspected numbered theorem is cited.

Schmidt's rank is different: [Bonato, Bruhn, Diestel and Spruessel, Twins of rayless graphs](https://arxiv.org/pdf/0911.3803), Section 2, Definition 2, p.3, uses deletion of a finite separator followed by ranks of the remaining components. Continuation height is not that invariant. Halin's and Schmidt's originals were not newly retrieved in full in this pass.

### Exact checked increment

The proof uses only reachable vertex/phase pairs `(v,k)`. Reachability is witnessed by a finite target prefix; all phase-zero states are included. An infinite continuation from such a state concatenates with its witnessed prefix to realize the whole target. Using all vertex/phase pairs could falsely count a tail from an unreachable phase.

| Checked endpoint | Contribution |
|---|---|
| `GenericOrdinalCertificate.avoids_iff_ordinal_certificate` | Avoidance iff a descending ordinal certificate exists on reachable states; arbitrary types; no branching hypothesis. |
| Natural-certificate endpoints in `GenericCertificate` | Under finite per-label branching, the least certificate is natural-valued and attained by actual finite continuations. |
| `GenericPruning.start_core_iff_realizes_from`, `realizes_iff_surviving_start` | A phase-zero state survives every finite round iff an actual full target path starts at that vertex. |
| `GenericPruning.matching_core_is_greatest_fixed_point` | The surviving core is the greatest fixed point of the successor operator under finite per-label branching. |
| `GenericMortalRank.matching_state_dichotomy`, `height_least`, `survives_iff_le_height` | Each state outside the core has a least attained finite height; it survives round n iff n is at most that height. No global avoidance premise. |
| `BlowUpRankInvariance.avoider_has_exact_rank_transport` | Every reachable copy in a complete finite-fibre blow-up has the projected original height under actual avoidance. |

The last item combines with complete-blow-up nonuniversality: one can defeat any prescribed countable host family while retaining all corresponding heights under projection. This is a corollary of checked endpoints, not a newly compiled combined endpoint. It shows a limitation of the heights after multiplicity and adjacency are forgotten. Full rank-labelled graphs are not asserted identical.

The finite-height argument is compactness/Konig reasoning; the exact pruning-height identity is a natural refinement. The publication case is the precise answer in Alexander's interface, the scope-correct formalization, the mixed-state decomposition, and the connection to the embedding invariant. The source did not demand a new hierarchy, but VibeMathed may judge a classical application insufficient for a discovery entry. The wording should enable that assessment.

### Two different constructions

Reachable matching states have finitely many successors under the stated hypothesis. The separate matching-history tree has an artificial root above every possible start, so that root has infinitely many children. It is outside the finite-branching argument. The older checked history-root calculation uses the binary natural-date interface; the generic history proof and Schmidt calculation are written results. Root ordinal rank omega and Schmidt rank 1 do not distinguish avoiders. No arbitrary-infinite-input decision algorithm, full structural classification or new Schmidt hierarchy is claimed.

**Significance:** The characterization identifies the exact boundary between infinite continuation and finite failure, and shows what structural information its heights omit.

## 4. Founder window: a mathematical replacement for common ancestry

The discovery is: **every organism still lies in a maximal admissible cluster when one common ancestor is replaced by a fixed real-time bound on all internal founders.** More strongly, any already admissible cluster extends to such a maximal one.

The predecessor is Alexander's Theorem 13. The present theorem retains IAP, convexity, connectedness and reflection, but fixes a nonnegative duration Delta and permits every internal founder born by the cluster's earliest birthdate plus Delta. The maximality class is thereby changed.

### Checked theorem and difficult obligations

[RealSpeciesTheorem.every_vertex_in_maximal_real_window](../../../real/RealSpeciesTheorem.lean) quantifies over every organism in a graph on natural-number identifiers, with literal real birthdates, finite strict earlier sublevels, strict parent-child chronology, and finite child sets. It requires no finite-root premise. This is a countably infinite presentation of the source biosphere. No arbitrary-vertex-type wrapper is included among the endpoints.

The formal chain proves:

- a connected, convex, reflecting IAP seed through each organism;
- closure of the required class under directed unions, with finite union-founders supplied by the fixed real window;
- a constrained Zorn extension for every existing admissible cluster;
- transport through an internally constructed chronological enumeration retaining original birthdates, ties, the same real duration, and every original maximality competitor.

The proof does not declare a descendant cone to be an IAP seed or assume a seed exists. The chain spans `FounderWindow`, `DirectedIAP`, `SeedIntersections`, `SpeciesSeed`, `RealFounderWindow`, `FounderMaximal`, `SpeciesReindex` and `RealSpeciesTheorem`, with 50 selected endpoints. The seed follows the source's maximal/minimal-set strategy; the additional closure and window argument supports the altered maximality class.

### Strictness witness and limitation

The [proof note](../../../notes/REAL-FOUNDER-WINDOW-THEOREM.md) gives edges `0 -> 2`, `1 -> 2`, and `n -> n+1` for every `n >= 2`. Give 0 and 1 birthdate 0, and later vertex n birthdate n-1. The whole graph is connected, convex, reflecting and IAP; its founders are coeval. Its window has duration zero, and no member is a common ancestor of both founders. Being the whole universe, it is maximal within the window class. This verifies strict enlargement mathematically, but the example is **written, not a separately registered Lean endpoint**.

Every common-ancestor admissible set satisfies the nonnegative window. Still, calling the result a generalization of Theorem 13 without describing the changed maximality class can mislead: maximality inside one class need not imply maximality in another. The exact statement is existence in the larger fixed-window class, without the common-ancestor requirement.

The same Delta applies to every competitor. Unrestricted maximal specieslike existence, uniqueness, a partition, effective recoverability and biological validation are not asserted. Informal Question 4 includes a plausibility component; a full biological closure claim would exceed the proof. The mathematical non-CA subquestion is directly answered.

**Significance:** Universal per-organism maximal-cluster existence survives relaxation from one common ancestor to several temporally bounded founders.

## 5. Verification and remaining publication gates

The live GitHub result for [Verify run 36631876391](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/actions/runs/36631876391) is `completed/success`, head `1592b89731d10fc49019ff22cf2f93c7bc799118`, updated `2026-09-29T21:18:45Z`. A read-only Git comparison found no changes from that commit to inspected main `ea70e6ce8f9476b5cabe275f7ce5fc0670adc1e3` under `real/`, `research/open-questions/embedding/`, `ordinal/`, or `continuation-2026-09-29/`. The machine ledger records hashes of the 15 relevant Lean files. This audit did not rerun Lean or recertify dependencies; it used the successful hosted checkpoint and verified source continuity.

The search comprised 16 recorded web queries plus targeted primary-text retrieval. It recovered the questions, classical machinery and published 2026 identity. It did not locate an independently verified earlier statement of all the population-specific refinements. That bounded outcome is not proof of priority. Search rankings supplied no stable totals or completeness measure; no exhaustive MathSciNet/zbMATH or citing-article survey was performed.

The remaining material gates are editorial and historical: expert reading of exact statements, application-versus-discovery judgment, and any further priority evidence. The founder strictness example's written status and the gated publisher-text comparison remain explicit. These do not erase the scoped theorems. No new source proved that the three directions had all already been solved elsewhere.

Recommended action is one substantive update to the existing entries, with exact source locators, predecessor attribution and revised discovery-first prose. Avoid duplicate entries. Author correspondence remains contingent on publication of the relevant VibeMathed entry, as requested.
