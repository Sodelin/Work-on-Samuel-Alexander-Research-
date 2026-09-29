# Bounded prior-art check: affinity-bias fixation rate

Checked 2026-09-25. Purpose: calibrate the claim accompanying the Lean package, not establish novelty or certify an exhaustive literature search. No proof sources were changed or compiled during this check.

**Conclusion.** The rate is a useful explicit consequence of the source model, robust to generation-dependent copying probabilities. Its general mathematical mechanism is elementary order preservation by a common nonnegative matrix. It should not be advertised as a new general contraction theorem. The bounded search did not locate an earlier statement of this exact source-model rate with arbitrary varying copying probabilities, but does not establish its absence or mathematical novelty. No author-designated open problem was identified as solved by this result.

## Exact result being compared

For the four-frequency affinity-bias recursions of Fogarty, Zhang and Feldman (2025), let s > 0 be constant, let each beta1(n), beta2(n) lie in [0,1], and initially let x1 > 0 and x3 > 0. Writing q(n) = x1(n) + x3(n) and

    r0 = max(x2(0)/x1(0), x4(0)/x3(0)),
    rn = r0 / (1+s)^n,

our checked theorem gives 0 <= 1-q(n) <= rn and q(n) -> 1. The checked odds lemma also yields the sharper deficit rn/(1+rn) by composition. The final `model_global_fixation` endpoint packages the weaker displayed bound and convergence. Copying probabilities may be chosen from state or history, provided their realized sequence obeys the interval constraints. This is a deterministic frequency model; it does not give finite-population fixation probabilities or a theorem about biological speciation.

## Three nearest primary sources and inspection limits

1. **Fogarty, Zhang and Feldman, “Gene-culture association and coevolution” (2025).** Available online 2025-08-23; *Theoretical Population Biology* 165, 62–71, October 2025. [DOI](https://doi.org/10.1016/j.tpb.2025.08.003); [author-institution PDF](https://pure.mpg.de/pubman/item/item_3667581_1/component/file_3667582/Fogarty_gene-culture_TheorPopulBiol_2025.pdf). Its full ten-page technical text, including appendices, was read in the source audit; local extraction was rechecked here. Section 3, pp. 66–67, equations (16a)–(19a) supplies the exact recursions. Equation (23) explicitly discusses fixation for equal copying probabilities. Section 3.1 restricts its nonzero-association equilibrium analysis to beta1,beta2 <= 1/2. I did not find the maximum within-background odds bound or an arbitrary time-varying probability theorem in that text. The new web open returned an internal error; the already acquired complete author PDF remained available locally.

2. **Fogarty and Otto, “Signatures of selection with cultural interference” (2024).** Online 2024-11-18; *PNAS* 121(48), e2322885121, issue 2024-11-26. [DOI](https://doi.org/10.1073/pnas.2322885121); [primary full text at PMC](https://pmc.ncbi.nlm.nih.gov/articles/PMC11621839/); [author-institution copy](https://pure.mpg.de/rest/items/item_3624528_3/component/file_3624538/content). This is the immediate affinity-bias model predecessor. The inspected model section and Table 2 allow genotype-specific copying rates; the article studies genetic hitchhiking and cultural interference, including genetic fixation probabilities and sweep dynamics. Its mating frequencies incorporate parental fitness, so stage ordering should be compared explicitly before identifying its entire update with the 2025 offspring-viability recursions. I found no exact max-odds/varying-probability theorem in the material inspected. This is only a partial-text negative result: indexed primary text and initial PMC sections were available, but later PMC requests produced a browser challenge and the author-PDF fetch returned 403. Its supplementary analysis was not comprehensively examined in this check.

3. **P. J. Bushell, “Hilbert's metric and positive contraction mappings in a Banach space” (1973).** December 1973; *Archive for Rational Mechanics and Analysis* 52, 330–338. [Publisher and DOI](https://link.springer.com/article/10.1007/BF00247467). This is a classical positive-operator contraction lead, not a verified exact theorem match. The publisher metadata and bibliography were accessible; the full PDF redirected to subscription access. Accordingly, no particular numbered theorem from this paper is claimed to subsume our result. Its relevance is the established positive-map comparison framework. Our calculation below is self-contained and needs no uninspected result from this source.

## Direct mathematical reduction: our comparison, not a quotation

Set u = (x1,x3)^T, v = (x2,x4)^T, and p = x1+x2. On the simplex, the affinity transmission step applies the same matrix to both trait vectors:

    M = [ 1-beta1*(1-p)     beta1*p      ]
        [ beta2*(1-p)       1-beta2*p   ].

All entries are nonnegative when p,beta1,beta2 are in [0,1]. Expanding the products reproduces the source preselection frequencies:

    Mu = (x1-beta1*D, x3+beta2*D)^T,
    Mv = (x2+beta1*D, x4-beta2*D)^T,
    D = x1*x4-x2*x3.

If v <= r*u coordinatewise, then M(r*u-v) >= 0, so Mv <= r*Mu. Selection and common positive normalization give

    u_next = (1+s)*Mu/Gamma,
    v_next = Mv/Gamma,
    v_next <= (r/(1+s))*u_next.

Iteration gives the checked rate. In this argument M may change every generation and depend on the current state or previous history: it need only be the same nonnegative matrix for both vectors at that step. No uniform mixing rate, irreducibility or strictly positive matrix entries are required. M is not generally stochastic; the proof does not assume it is.

This is a one-sided maximum-ratio comparison. It should not be described as a new Hilbert-projective metric contraction coefficient: projective distance measures a ratio spread and is invariant under separate positive rescaling of its arguments, whereas the factor 1/(1+s) here comes directly from the selective rescaling. The division-free inequality remains the clean statement when boundary coordinates are present.

## Search log and claim calibration

Six focused web queries, in two batches:

1. `"affinity bias" "fixation" "Fogarty" odds`
2. `"gene-culture" "global" "convergence" affinity`
3. `"positive linear" "max" "ratio" "nonexpansive" Hilbert Bushell`
4. `"positive linear" "M(Ax/Ay)"`
5. `Bushell 1973 Hilbert metric positive contraction mappings max ratio pdf`
6. `"Signatures of selection with cultural interference" "affinity" fixation`

Direct follow-up opens were limited to the three selected papers; follow-up text searches within PMC were blocked by its browser challenge. Secondary search results were used only for navigation. No access controls were bypassed, citation-network census performed, or new literature/proof lane opened.

Recommended package wording: **“We derive and machine-check an explicit fixation bound for the published affinity-bias recursions, valid for arbitrary generation-dependent copying probabilities under the stated initial positivity and constant-selection assumptions. The proof uses a standard nonnegative-matrix comparison. Priority of this source-specific statement has not been established.”**

Avoid: “a new general contraction principle,” “the first global-fixation proof,” “a named open problem solved,” or “proof that behavioral feedback causes speciation.” Establishing priority would require a fuller examination of the predecessor's supplement and older gene-culture selection literature. That is separate from the completed mathematical verification.
