# Proposed revisions to the seven pending entries

These are the coordinator-reviewed fields for the existing VibeMathed queue. Each record identifies its original title so the curator can apply the revision without creating another entry. Proof links, solve dates, AI attribution and the requested verification tier remain as recorded in the original submission. Publication status and delivery receipts are tracked in the [submission manifest](../../PUBLIC-SUBMISSION-MANIFEST.json).

The [source-question audit](README.md) explains the contribution, closest predecessors, formal scope and remaining uncertainties. The exact field strings and limits are in [REVISIONS.json](REVISIONS.json). This document presents a request for editorial assessment, not a catalog acceptance claim.

## An exact finite-population reversal of genetic and epigenetic barriers

**Existing queue title:** Finite offspring sampling reverses a genetic-epigenetic barrier ordering

**Entry key:** `finite-epigenetic`

### Question and assumptions

Can finite offspring sampling reverse the ordering of genetic and epigenetic neutral-marker barriers in a matched extension of Planidin et al. (2025)? Their Section 5 proposes finite-population extensions; this project formulates and resolves an exact special case. Two demes each contain one diploid adult, with migration m=1/4, additive selection s=1/2 and recombination r=1/2. Both comparisons start from locally adapted selected states and use one preselection migrant-marker pulse, followed by continuing migration. Mutation-free genetic inheritance is compared with complete environmental induction after mating. Offspring are sampled independently from normalized reproductive pools, permitting selfing. The target is the sign of the fixation-based epigenetic-minus-genetic barrier and its relation to the matched deterministic sequence, using the common preselection dose B0=1/8.

### Result and contribution

Finite sampling changes the ordering: p_gen=323808055/4466354606 and p_epi=1/14, so RI_gen=937945083/2233177303 < RI_epi=3/7, with RI=1-p/(1/8). The advantage is exactly 19130904/2233177303. Harmonic certificates identify the finite-model limits with error <=(99/100)^n. In the matched deterministic recurrence, the genetic barrier is above 3/7 at every biological generation from four onward, while pure induction gives 3/7. Thus the checked comparison combines a finite stochastic limit with a uniform deterministic finite-time ordering. Its useful increment is a fully specified, exact comparison with a controlled tail. Finite epigenetic models, population-size-dependent advantages and normalized fixation measures have prior literature; the particular matched ordering is the candidate contribution.

### Verification

Lean 4.33.1 and pinned Mathlib; 34 selected declarations across four modules, including supporting lemmas. The finite kernel proof checks normalization, boundary closure, rational harmonic identities, pulse values and the geometric limit bound. DeterministicEpigenetic certifies the ordering at every biological generation >=4; RankingReversal combines the two comparisons. All four source hashes matched the existing receipt on 29 September 2026. Hosted Verify run 36173386580 succeeded at submitted commit a2644182b147eb40816abb278e00c3c6d4709eb8. The old local receipt retains its recovered-exit caveat; no new Lean compilation was run for this literature update. Allowed axioms are propext, Classical.choice and Quot.sound. The phased-to-count and full-to-reduced correspondences have written derivations and exact rational checks. Deterministic common-limit existence has a written internally audited proof, outside these Lean modules. This audit reconciles publication-only manifest differences and leaves all theorem sources unchanged. Internal review is distinct from independent human statement review. Requested status: Partial result; Lean-checked, statement unaudited.

### Context for editorial assessment

The contribution is an exact ordering reversal under a declared model change, with a finite fixation proof and a matched deterministic comparison. This update closes the earlier Smithson access gap: the author's WSU dissertation Chapter 1 supplies full model and stochastic-analysis text, with a publisher-version caveat. Smithson already studies drift-dependent adaptation benefits; Greenspoon already studies finite stochastic epigenetic speciation; Muirhead and Presgraves already normalize neutral-marker fixation. Our source map distinguishes their observables and life cycles from the exact fixation-barrier question here. Planidin's Section 5 is the published research direction; the specific parameter question is project-formulated. Please assess the exact increment on this evidence. Worldwide priority and independent human review remain unestablished.

[Specialist field record](finite-barrier/VIBEMATHED-FIELDS.json).

## One complete genome-copy history, two diploid pedigrees with opposite identical-ancestor properties

**Existing queue title:** Identical genome-copy transmission histories with opposite organism-level IAP

**Entry key:** `genome-ownership`

### Question and assumptions

Does retaining every realized genome-copy transmission determine Alexander's whole-population identical-ancestor property (IAP) when organism ownership is known through any prescribed finite generation? IAP means that each organism has finitely many descendants or finitely many non-descendants within the population. The candidate class has four diploid organisms per generation, exactly four founders, two distinct parents per nonfounder, exactly two children per organism, weak connectivity and real generation birthdates. Every pedigree edge must be witnessed by a recorded transmission. Ownership groups each generation's eight labelled copies into four pairs. This exact inverse-observation question was formulated in this project; Alexander supplies the ancestry predicate, while Wong supplies the finite genome-ARG interface. The fixed observation omits later ownership and includes one unrecombined abstract genomic region.

### Result and contribution

A constrained counterexample answers no. For every N, two ownership schedules agree through N on the same complete eight-lane copy history. Both satisfy all listed degree and diploidy conditions; even per-copy binary sex labels agree and each nonfounder has opposite-sex parents. One whole pedigree has IAP and is maximal specieslike; the other's permanently separated tail violates IAP although the whole graph remains weakly connected. Hence no exact decoder, even noncomputable, works on this family. An explicit two-edge witness explains the obstruction: exact transmission images preserve pedigree edges without lifting organism ancestry paths. Finite truncations are checked against the Wong gARG structure. The contribution is this conjunction and its infinite-IAP consequence. Established pedigree ambiguity is credited. This realized-history theorem supplies no equality of genotype likelihoods or probability claim for infinite schedules.

### Verification

Lean-checked; statement not independently audited by a human expert. Lean 4.33.1 freshly compiled 31 project modules and audited all 77 public theorem declarations of the three new construction/bridge modules at proof commit 1ba951e4417c930e76ef0f5ace747c9ccb681338. Public evidence head 4ab00a2932f3efdb7091c9a526af4bcd25cc8cd2 has successful hosted runs 36298049178 and 36298049071 in the existing record. On 29 September 2026 this publication audit reran check_packet.py: all saved source/log hashes and the 77-theorem inventory passed. That integrity check is not a new Lean compilation. The main endpoints are constrained_counterexample, no_iap_decoder, owner_exactly_two, edge_exact_image, parents_opposite_sex, same_copy_sex and generation_dated_biosphere. Recorded axioms are limited to propext, Classical.choice and Quot.sound. A fresh bounded primary-source comparison confirms the need to distinguish Thatte's potential-parent graph, Kirkpatrick's likelihood framework and optional individual metadata in tskit. Worldwide priority remains unestablished.

### Context for editorial assessment

Please assess this as an explicit information-loss construction applying Alexander's IAP to realized copy-transmission records. Its force comes from simultaneously retaining every transmission, exact witnessed organism edges, diploidy, two parents/two children, weak connectivity, shared sex annotations and arbitrarily long ownership agreement. The exact constrained question is project-posed: no source author is credited with posing it, and no named general pedigree-reconstruction question is declared closed. The companion sampling theorem gives a precise recovery boundary for the same family. The prior-art audit supports a candidate incremental contribution, not a claim that genomes cannot reveal ancestry. Consider the two entries as one coordinated result pair if that better fits catalog policy.

[Specialist field record](genome-ownership/VIBEMATH-DRAFTS.json).

## Exactly which ownership samples recover identical ancestry in a delayed-split pedigree family?

**Existing queue title:** An exact ownership-sampling criterion for delayed-split identical ancestry

**Entry key:** `ownership-sampling`

### Question and assumptions

For the checked diploid family consisting of perpetual mixing or a single permanent split after an even generation S >= 2, which static sets T of co-ownership observation times identify whole-population IAP? The complete realized copy-transmission graph is known. A noiseless observation at t asks whether named lanes 0 and 3 belong to the same organism; unsampled times are distinct from negative answers. The target is identification from the entire masked record. Also consider the additional prior assumption that any switch occurs by a known even B >= 2. This question is a project continuation of the ownership counterexample, using Alexander's IAP definition. It is not an externally posed general sampling conjecture.

### Result and contribution

The criterion is exact: the complete record identifies IAP if and only if sampled odd generations are unbounded. This separates timing from volume: even the entire ownership assignment at every even generation fails, while arbitrarily sparse unbounded odd samples suffice. A positive observation certifies the split branch; finitely many negative observations permit a later split. Under the supplied even switch bound B >= 2, identification holds exactly when T contains an odd time after B, so one query at B+1 suffices. The proof follows from the explicit query law: always false under mixing, and true exactly at odd times beyond the split. This sharp recovery boundary belongs to the stated family. The infinite-record decoder is a proposition-valued mathematical function, not a uniformly terminating algorithm. Finite/infinite monitoring distinctions are established prior mathematics.

### Verification

Lean-checked; statement not independently audited by a human expert. Exact-clean-commit Lean 4.33.1 audit at c071d4b895b8fe979211b68ac30240f8833e707d covers five project modules and 20 selected axiom reports: 15 new observation endpoints plus five reused construction endpoints. Public checkpoint 35a8f86b5f0e555eab25d003353c0c8772578db5 preserves the source and evidence. On 29 September 2026 this audit reran verify_packet.py successfully, validating source/commit correspondence, compiler logs, 22 artifact hashes and the allowed axioms propext, Classical.choice and Quot.sound. This was saved-receipt verification, not a new compiler or hosted run. Core endpoints are identifies_iap_iff, no_even_ownership_decoder, bounded_identifies_iap_iff and bounded_iap_iff_one_query. The iff with a bounded switch requires B even and B >= 2. The observation mask is static and the lane identities and specimen ownership are exact. The theorem does not derive those inputs, the family assumption or the switch bound from data.

### Context for editorial assessment

This is the sharp observation-recovery half of the ownership result pair: a complete classification of static masks for IAP within its explicit delayed-split family, strengthened by failure of all even-generation ownership and a conditional one-query threshold. Its proof is a short exact deduction once the constrained construction is established; the main mathematical burden lies in that construction and source bridge. Bauer's finite-witness monitorability framework is credited for the general finite/infinite distinction; our theorem has different quantifiers and classifies observation masks for this fixed family. No general monitoring, likelihood, biological applicability or worldwide priority claim is made. Please link with the ownership entry or assess them together if preferred.

[Specialist field record](genome-ownership/VIBEMATH-DRAFTS.json).

## Exact family-recovery probabilities and the role of independent inheritance blocks

**Existing queue title:** Exact sampled-family recovery from independent binary inheritance blocks

**Entry key:** `sampled-family-recovery`

### Question and assumptions

For a fixed one-generation sample, what is the exact chance that observed symbol-sharing components recover every true family? Families have disjoint parental pairs and nonempty sizes m_i. At each block all parents have distinct symbols; children copy either parent fairly and independently across children, blocks and families. Observations are exact. Join children if they match at any of B>=1 corresponding blocks, then take components. Also ask whether preserving every single-block joint distribution, without independence between blocks, preserves the gain from extra blocks. This is a project-formulated finite benchmark motivated by Kim, Mossel, Ramnarayan and Turner's reconstruction model. Its dependence example is relevant to their Section 1.6 Question 1, which remains broader than this target.

### Result and contribution

The exact success probability is product_i[1-(2^(m_i-1)-1)/2^(B*(m_i-1))]. Recovery is proved directly for the observed-symbol output law. A family disconnects exactly when its inheritance vectors occupy one complementary pair, both present; an explicit bijection counts the failure event. For three siblings and two blocks, success is 13/16, versus 7/16 for the project's restricted all-three-sharing rule. Repeating one fair parental choice per child across all blocks preserves every block's full joint law, yet this family's component-recovery probability stays 1/4 for every B>=1. Extra observations preserve existing paths, but correct marginals alone do not guarantee an independence-based probability gain. The result supplies an exact finite control and a one-family dependence example; it makes no all-estimator impossibility or REC-GEN improvement claim.

### Verification

Lean 4.33.1, pinned Mathlib, exact clean proof commit ae0beee8d04e32c45f28d2f465b924d6816c82a5. Seven modules and 31 selected declarations cover the graph characterization, explicit finite probability law, observed-output recovery and repeated-block counterexample. On 29 September 2026 the saved-evidence verifier passed: source and compiler-log hashes, 49 artifact hashes, and selected axiom reports. This was an integrity replay, not a new compiler run. Allowed axioms: propext, Classical.choice, Quot.sound. The output-law endpoint requires a finite measurable alphabet with measurable singletons and injective parent symbols at each block. The repeated-law success endpoint is for one family. Distribution identifiability, observation-error coupling, parent-couple construction and an executable refinement are outside these endpoints. Internal statement review is recorded separately. No full REC-GEN formalization or coupling from Wong's continuous ARG law is claimed. Requested tier: Lean-checked, statement unaudited.

### Context for editorial assessment

Please assess the exact finite benchmark and dependence construction on their stated merits. The source-question audit now maps all three directions of KMRT Section 1.6 Question 1. The positive theorem retains symbol injectivity and block independence; its repeated-block law gives a boundary example for this estimator, not closure of the general non-i.i.d. question. A finite symbol type does not solve the collision-allowing finite-alphabet problem. Mossel-Vulakh Section 3.2 already uses pairwise candidate screening; our 13/16 versus 7/16 compares two project-restricted procedures. The accepted packet explicitly makes no novelty claim, and prior open status of this exact finite question has not been established. This source mapping clarifies the existing submission; catalog eligibility remains for editorial assessment.

[Specialist field record](sampled-family/VIBEMATHED-FIELDS.json).

## No countable universal family of avoiding populations, even with exact parent counts

**Existing queue title:** No countable universal family of avoiding populations, even with exact parent counts

**Entry key:** `universal-avoider`

### Question and assumptions

Can populations avoiding a fixed infinite label sequence be represented inside one universal population, or a countable family? Alexander poses the universality direction in Biologically Unavoidable Sequences (2013), Section 6, p. 12, by analogy with Cherlin and Shelah. Here an embedding is an injective map preserving adjacency after forgetting directions and labels. Populations are infinite genealogies with finitely many roots, finite children, real birthdates increasing along edges, finite birth sublevels, and a parent of every label at every nonroot. We ask whether universality is possible even within the subclass having exactly one incoming parent of each label. This is the ordinary subgraph-embedding interpretation of a source question that does not prescribe one category.

### Result and contribution

No countable catalogue suffices. From any population avoiding s, the checked construction produces another avoider with the same roots and exactly one parent of each label at every nonroot that embeds into none of any prescribed countable family of population hosts. It defeats every injective map with any finite global bound on edge stretch. Parent selection preserves avoidance; terminal cloning preserves the selected infinite-word language exactly. If the original population already has the required parent counts, selection is unnecessary and its entire language is retained. The essential population-specific step preserves chronology, finite pasts, roots and exact incoming-parent sets while creating enough vertices to defeat finite host balls. The graph-growth obstruction is classical. The result permits terminal individuals and unbounded finite child counts; it does not settle fixed child caps or arbitrarily unbounded edge stretch.

### Verification

Lean 4.33.1 with Mathlib pinned to 0df444a360eaa60ab8c11dca51a86af692955474. TerminalCloneAvoiders.lean contains 16 selected endpoints for the population construction, exact parent counts, root correspondence, language preservation/inclusion, and obstruction. The earlier GenericUniversalAvoiders.lean has 10 selected endpoints. All were covered by successful hosted Verify run 36631876391 at commit 1592b89731d10fc49019ff22cf2f93c7bc799118. This audit read the strongest endpoint hypotheses and checked that the relevant sources are unchanged at main ea70e6c; it did not rerun the compiler. Reported proof dependencies use only propext, Classical.choice and Quot.sound. Endpoint counts measure verification coverage. Internal agent reviews do not establish independent human verification or worldwide priority. Requested label remains Lean-checked, statement unaudited.

### Context for editorial assessment

The contribution is a negative answer to the explicit ordinary-embedding interpretation of Alexander's question, strengthened to exact incoming-parent counts. Cherlin-Shelah supplies the embedding convention. Lehner (2023), citing de Bruijn through Rado, supplies the classical local-finiteness context. Nonuniversality for all locally finite graphs alone does not prove it for this restricted population subclass; the preservation construction supplies that step. Present the countable-family and finite-stretch conclusions as proved refinements, not as newly invented diagonalization. Parent selection may shrink the original language, so exact language equality is claimed only for cloning itself or when selection is unnecessary. No claim of resolving every embedding category or historical priority is made.

[Specialist field record](alexander/VIBEMATHED-REVISIONS.json).

## Exact ordinal certificates and pruning characterize sequence realization

**Existing queue title:** Ordinal certificates and exact pruning characterize sequence realization

**Entry key:** `ordinal-realization`

### Question and assumptions

Which infinite labelled populations realize a specified sequence? Alexander (2013), Section 6, p. 12, asks for such a characterization and singles out ordinal numbers, by analogy with Schmidt's rayless-graph rank. We give an exact characterization on reachable vertex/phase states: (v,k) is included precisely when a finite path spelling the first k letters can end at v. A transition follows an edge labelled by the next required letter. The ordinal criterion works for arbitrary vertex and label types without finite branching. When each state has finitely many matching successors, an additional question is exactly which states survive repeated deletion of states with no surviving child, and what measures the continuation length of a deleted state.

### Result and contribution

Avoidance is equivalent to a strictly decreasing ordinal certificate on reachable states. With finite per-label branching, natural certificates suffice. Repeated pruning has a greatest fixed-point core: a starting state survives every finite round exactly when an actual infinite path spells the whole sequence from that vertex. Outside the core, even in a population that also has realizers, each state has an attained maximum continuation length h, the least natural decreasing certificate; it survives round n exactly when n <= h and is removed at h+1. Complete finite-fibre blow-ups preserve every corresponding least matching height. Thus those heights, after forgetting multiplicity and adjacency, do not determine the embedding obstruction. The rank and compactness methods are classical; this is a precise source-specific characterization and invariant analysis, with no arbitrary-infinite-input decision algorithm or new Schmidt-rank hierarchy claimed.

### Verification

The generic certificate chain has 8 natural-certificate and 3 ordinal-certificate selected endpoints. The September 29 extension adds 10 pruning, 9 mortal-rank and 7 rank-transport selected endpoints. The decisive endpoints include avoids_iff_ordinal_certificate, realizes_iff_surviving_start, matching_state_dichotomy, survives_iff_le_height and avoider_has_exact_rank_transport. Successful hosted Verify run 36631876391 checked the sources at commit 1592b89731d10fc49019ff22cf2f93c7bc799118; the audited files are unchanged at main ea70e6c. Lean 4.33.1 and pinned Mathlib 0df444a360eaa60ab8c11dca51a86af692955474 were used. Standard reported axioms only. This publication audit checked statement correspondence and prior-art context without recompiling. The generic ordinal theorem directly applies Mathlib's well-founded rank. Schmidt rank is a distinct invariant and is not formalized by these endpoints. Requested label remains Lean-checked, statement unaudited.

### Context for editorial assessment

The source asks for a characterization, not specifically a new transfinite hierarchy. This result gives exact membership, pruning, least finite heights, and a checked limitation of those heights as structural invariants. The underlying rank characterization and finite-branching compactness are established mathematics; the submission should be assessed as an application to Alexander's explicit question with formal refinements. The artificial root of the separate history tree has infinite branching and cannot be inserted into the finite-branching state theorem. Its ordinal rank omega and written Schmidt rank 1 do not distinguish avoiders. We retain partial scope for the broader analogy and do not advertise a new general termination theorem or classification up to graph embedding.

[Specialist field record](alexander/VIBEMATHED-REVISIONS.json).

## Maximal specieslike clusters without a common ancestor, using a fixed founding window

**Existing queue title:** Maximal specieslike clusters with a fixed real founding window

**Entry key:** `founder-window`

### Question and assumptions

Can every organism inhabit a maximal specieslike cluster under constraints that do not require a common ancestor? Alexander's Specieslike clusters based on identical ancestor points (2026), Section 6, proves an existence theorem using common ancestry and reflection, then explicitly asks for alternatives without common ancestry. For each fixed real Delta >= 0, we replace common ancestry by a founding-window condition: all internal founders of a cluster are born within Delta of its earliest member. A founder has no strict ancestor inside the cluster; it need not be parentless in the ambient graph. We retain connectedness, ancestry convexity, the identical ancestor point property (IAP), and reflection. The ambient graph has natural-number identifiers, real chronological birthdates with finite strict earlier sublevels, and finitely many children per organism.

### Result and contribution

Every organism belongs to an inclusion-maximal cluster with IAP, convexity, connectedness, reflection and the prescribed real founding window. More strongly, every cluster satisfying those requirements extends to a maximal one. The same Delta applies to every competitor. The proof supplies a genuine seed through each organism, proves preservation under directed unions, and transports maximality back to the original real birthdates, including ties. A written two-founder merging-ray example satisfies the zero-duration window and all retained conditions but has no common ancestor, so the replacement strictly enlarges the admissible class. This answers the mathematical non-CA direction. Maximality is within the fixed-window class; uniqueness, a species partition and biological plausibility of the window are not established.

### Verification

The eight founder-window modules contribute 50 selected endpoints to the 151-endpoint real/Mathlib audit. The strongest public endpoint is RealSpeciesTheorem.every_vertex_in_maximal_real_window; maximal_window_extension proves extension of every existing admissible cluster. The seed, directed-union IAP, real-window closure, constrained Zorn argument and faithful reindexing are checked. Successful hosted Verify run 36631876391 covers commit 1592b89731d10fc49019ff22cf2f93c7bc799118, and these real sources are unchanged at main ea70e6c. Lean 4.33.1, Mathlib 0df444a360eaa60ab8c11dca51a86af692955474, with only standard reported axioms. The two-founder example establishing strict weakening is a written argument in REAL-FOUNDER-WINDOW-THEOREM.md, not one of these Lean endpoints. This audit inspected source correspondence without recompiling. Requested label remains Lean-checked, statement unaudited; no independent human expert review or worldwide priority is claimed.

### Context for editorial assessment

The exact target is the paragraph after Theorem 13 in arXiv:2602.05274v1, Section 6, p.17. Informal Question 4 on p.9 also requests biological plausibility, which this mathematical theorem does not certify. The article is published in Journal of Mathematical Biology 92, article 41 (28 February 2026), DOI 10.1007/s00285-026-02361-x; the publisher full text was gated, so the exact wording was checked in the accepted arXiv manuscript. Our result changes the admissible maximality class. It does not claim that every organism lies in an unrestricted maximal specieslike cluster. Its strongest presentation is that common ancestry can be replaced by a literal real-time bound on internal founders while retaining universal per-organism existence. Keep the original 25 September 2026 solve date.

[Specialist field record](alexander/VIBEMATHED-REVISIONS.json).
