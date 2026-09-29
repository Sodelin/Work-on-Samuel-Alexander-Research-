# Open-problem source audit: epigenetic and gene-culture models

Audit date: 2026-09-25. Scope: a bounded full-text check of the requested sources, not a literature-wide novelty determination. The initial source audit made no repository source changes, Lean builds, or outreach; the subsequent authorized formalization is recorded below.

**Result:** genuine author-proposed mathematical extensions were located, but neither paper states a precise unresolved conjecture that the current baseline package can already be said to solve. A short, source-grounded equilibrium refinement is available below. It is a proof clarification and parameter-range extension, not an established new open-problem solution.

## Acquired sources and reading coverage

1. Fogarty, Zhang and Feldman, *Gene-culture association and coevolution*, Theoretical Population Biology 165, 62–71. DOI [10.1016/j.tpb.2025.08.003](https://doi.org/10.1016/j.tpb.2025.08.003). Online **2025-08-23**, issue October 2025. The full **10-page** published paper, including Appendix A and Appendix B, was read. Official [Max Planck repository PDF](https://pure.mpg.de/pubman/item/item_3667581_1/component/file_3667582/Fogarty_gene-culture_TheorPopulBiol_2025.pdf); [author institutional publication record](https://cehg.stanford.edu/publications/gene-culture-association-and-coevolution). Saved in the working research collection as Fogarty-Zhang-Feldman-2025.pdf and extracted .txt; those source copies are not redistributed in this review archive.

2. Planidin et al., *Adaptive epigenetic divergence can facilitate ecological speciation*, Proceedings B 292, 20251217. DOI [10.1098/rspb.2025.1217](https://doi.org/10.1098/rspb.2025.1217), publication **2025-09-17**. Full main text was read through the now-accessible [PMC article](https://pmc.ncbi.nlm.nih.gov/articles/PMC12440623/). The complete **58-page** supplement was downloaded from the official [Figshare article](https://api.figshare.com/v2/articles/29875972), [file 57066856](https://ndownloader.figshare.com/files/57066856), version 1, posted **2025-08-09**; PDF internal date **2025-07-04**. Reading covered its contents, exact life-cycle recursions pp. 3–5, and spectral derivation/worked example pp. 33–38. Other supplement pages were not fully audited. Saved in the working research collection as Planidin-2025-supplement.pdf and extracted .txt; those copies are not redistributed here. Source code archive is [Zenodo 16635603](https://doi.org/10.5281/zenodo.16635603), identified but not executed.

Official repositories/APIs worked without access-control workarounds. No need to rely on the earlier inaccessible wrapper.

## What the authors actually leave open

**Planidin: an explicit extension direction, not a proved prediction.** Conclusion §5 states: “Finite population models may magnify the relative strength of epigenetic barriers to gene flow.” This is a 14-word quotation. Section 4(a) identifies evolution of epigenetic inheritance during the proposed RI feedback as not yet explicitly explored in that context. Section 1 also proposes interacting loci and other barriers. These are mathematical modelling directions; they are distinct from the empirical question of whether adaptive epigenetic effects cause RI in nature.

Its baseline is deterministic, infinite-population, two-deme, diploid and two-locus. Epimutation uses alpha=mu(1+phi), beta=mu(1−phi), reversed between demes. Life order is migration, selection, recombination, gamete formation/mating, epimutation. RI=1−B_hat/B_0 uses a one-time neutral migrant marker; it is not a species-membership definition. Supplement pp. 33–38 already derive a constant-linear-life-cycle spectral solution for asexual haploids. Generic “solve a constant transition matrix” work would duplicate that existing result.

**Fogarty: nonvertical transmission remains model-dependent.** Discussion p. 68 states: “the effect of non-vertical transmission (i.e. weakening or strengthening GCA) would depend on its exact formulation.” This is a 20-word quotation. The paper gives two deterministic haploid vertical-transmission models: cultural-trait bias and affinity bias. It derives invasion criteria, neutral-selection polymorphism, and affinity equilibrium conclusions. Weak-selection persistence is discussed on pp. 64 and 67 and illustrated numerically in Fig. 5, p. 69; it is not labelled an open conjecture. An explicit nonvertical kernel would have to be chosen before a theorem could answer that proposed direction.

The closest finite-population gene-culture work is already [Fogarty and Otto (2024), *Signatures of selection with cultural interference*](https://doi.org/10.1073/pnas.2322885121), [author PDF](https://pure.mpg.de/pubman/item/item_3624528_3/component/file_3624538/Fogarty_Signatures_PNAS_2024.pdf). It treats cultural effects on genetic fixation probabilities and sweep dynamics. This was checked through primary-source technical passages, not fully audited here. A generic claim to be the first finite-population gene-culture analysis is therefore untenable.

For Planidin's inheritance-feedback direction, its cited antecedents include [Furrow–Feldman 2014](https://doi.org/10.1111/evo.12225), [Uller–English–Pen 2015](https://doi.org/10.1098/rspb.2015.0682), and [Greenspoon–Spencer 2018](https://doi.org/10.1111/evo.13619). Their existence and relationship are reported by the 2025 paper; their full mathematical results were not independently re-audited here. A modifier-invasion project must compare against them before making a novelty claim.

## Exact source-based model available for a bounded theorem

Use Fogarty's affinity-bias model, Table 2 and Eqs. (17)–(23), pp. 66–67. For x_i >= 0 with sum_i x_i=1, set

    p = x1+x2, q = x1+x3, D = x1*x4−x2*x3,
    z = q+(beta2−beta1)*D, Gamma = 1+s*z.

The recursion is

    Gamma*x1' = (1+s)*(x1−beta1*D)
    Gamma*x2' = x2+beta1*D
    Gamma*x3' = (1+s)*(x3+beta2*D)
    Gamma*x4' = x4−beta2*D.

Here 0 <= beta1,beta2 <= 1 are copying probabilities and s>0. These equations define the specific theorem target; they are not an arbitrary feedback recurrence fitted to the user's idea.

### Written proof clarification and stronger parameter range

**Proposition (derived in this audit; subsequently Lean-checked on 2026-09-25).** For the above recursion, no fixed point has both 0<p<1 and 0<q<1. The entire probability range beta1,beta2 in [0,1] is permitted.

This claim does not imply global convergence, an explicit convergence rate, or reproductive isolation. It rules out simultaneous genetic and cultural polymorphism at a fixed point for this particular affinity model.

**Proof.** The preselection frequencies

    y1=x1−beta1*D, y2=x2+beta1*D,
    y3=x3+beta2*D, y4=x4−beta2*D

are nonnegative and sum to one. For example, when D>=0, y1>=x1−D=x1*(1−x4)+x2*x3>=0, and y4>=x4−D=x4*(1−x1)+x2*x3>=0; the other two are immediate. When D<=0, the analogous bounds use x2+D=x2*(1−x3)+x1*x4 and x3+D=x3*(1−x2)+x1*x4. Thus 0<=z=y1+y3<=1 and Gamma>=1.

Define k=1−beta1*(1−p)−beta2*p. Direct substitution, using x1=p*q+D, yields

    p'−p = s*D*k/Gamma.

At a fixed point, s>0 and Gamma>0 imply D*k=0.

If k>0, D=0. The q recursion then gives

    q'−q = s*q*(1−q)/(1+s*q)>0,

contradicting 0<q<1 and fixedness.

If k=0, write k=(1−p)*(1−beta1)+p*(1−beta2). Both summands are nonnegative; since 0<p<1, both beta1 and beta2 equal 1. Hence beta2−beta1=0 and the same strict inequality for q'−q follows, regardless of D. Those cases exhaust k>=0. QED.

**Why this is useful but should be described modestly.** Section 3.1 of the source restricts its argument to beta1,beta2<=1/2 and rules out an interior equilibrium. Its last displayed inequalities alone do not establish the claimed contradiction: Gamma>1 and a second positive expression exceeding 1 can coexist. The independent argument above avoids that inference and covers the full probability range. Treat this as an internal proof-audit observation until the source equations, proof and formal endpoint have independent review. It does not establish that the broader result is absent elsewhere in the literature.

The bounded Lean scope is unusually clear: simplex preservation, the p drift identity, the nonnegative k decomposition, and absence of polymorphic fixed points. It needs neither stochastic convergence nor biological extrapolation.

## A genuine open-direction contract, if the larger project proceeds

For Planidin's finite-population suggestion, the next meaningful question would be:

> In a fully specified finite, two-deme stochastic counterpart of the published life cycle, when does epigenetic induction reduce neutral migrant-marker transmission more than the matched genetic model, and how does this comparison depend on population size?

This is a proposed precise research programme grounded in the authors' direction, not a theorem already present or a claim that the authors conjectured a universal inequality.

Before a proof, specify all of the following:

- The finite census size, diploid parent sampling, migration sampling, viability selection, recombination, and epimutation timing. Different choices can change the answer.
- The finite analogue of RI. Eventual expected marker frequency, fixation probability, and a fixed-horizon marker statistic are different objects. Equating them requires an absorption or convergence argument.
- Matching of the genetic and epigenetic models, initial backgrounds, and whether comparison is conditional on marker introduction or on survival.
- Whether the goal is an exact small-population counterexample to universal monotonicity, or a restricted comparative theorem with explicit parameter conditions.

A realistic first experiment is an exact rational transition matrix for a very small population, followed by a rigorously certified absorption calculation and a comparison counterexample if one exists. It would probe the authors' “may” statement rather than assert that finite size must strengthen isolation. No such calculation was run in this audit. A standard concentration bound between a finite stochastic process and a deterministic recurrence would not, by itself, answer this comparison.

For Fogarty, adding a nonvertical kernel and proving its effect on association is likewise a legitimate extension, but the kernel is a scientific modelling choice. A theorem about a convenient invented kernel must be labelled that way, rather than presented as the resolution of a pre-existing named problem.

## Search and evidence limits

Initial exact queries:

1. "10.1098/rspb.2025.1217"
2. "Fogarty" "Zhang" "Feldman" "2025" "Gene-culture association"

Bounded follow-up queries:

3. "Gene-culture association and coevolution" "horizontal" "2026"
4. "Adaptive epigenetic divergence" "finite population" "2026"
5. "Signatures of selection with cultural interference" "2024"

Direct acquisition followed the Max Planck repository, PMC, the official Figshare collection 7973908/article 29875972 API, and source references. Follow-up queries did not establish a later solution to the proposed extensions; that negative result is not evidence that none exists. The Fogarty proof refinement was derived directly, not selected because a search failed to find its proof.

A memory-registry query for Planidin/Fogarty/gene-culture/speciation returned no relevant hit. No memory facts were used. The two paper downloads and this note are the only project artifacts written by this audit.




## Subsequent formalization receipt (2026-09-25)

The bounded proof task following this source audit is complete in ../feedback-speciation/affinity-lean/. FogartyAffinity.lean and FogartyAffinityFixation.lean both compiled with Lean 4.33.1, one worker and a 4096 MB cap, against the existing pinned Mathlib cache. Eighteen selected endpoints printed only propext, Classical.choice, and Quot.sound. No sorry, admit, or custom axiom occurs in either source. Successful output and source hashes are preserved in that directory.

The original fixed-point refinement above is now machine checked directly from the four source equations. An independent agent also compared the base module with the full published equations and reviewed the beta1=beta2=1 boundary.

The subsequent quantitative refinement proves more: if beneficial culture initially occurs in both genetic backgrounds, define r0=max(x2(0)/x1(0),x4(0)/x3(0)). For arbitrary sequences beta1(n),beta2(n) in [0,1] and constant s>0, source-recursion trajectories satisfy 0<=1-q(n)<=r0/(1+s)^n, and q(n) tends to one in the epsilon sense. An actual recursively defined evolution realizes the model. Both transmission-margin identities, the odds contraction, and the convergence argument were checked; the odds recurrence was not assumed.

This addresses a definite mathematical property of the cited affinity model. It does not turn the proposed finite-population or nonvertical-transmission directions into solved author-designated open problems. Priority and publication significance remain unverified.

