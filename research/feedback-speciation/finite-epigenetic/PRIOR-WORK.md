# Prior work and interpretation gates for a finite epigenetic barrier model

Audit date: 2026-09-25. Bounded primary-source investigation for the proposed finite-population extension of Planidin et al. (2025). This note is separate from the frozen version-2 archive. No simulations, source-code execution, compilation, or proof implementation were performed.

**Disposition.** A source-faithful finite-population comparison of the epigenetic and matched genetic barriers remains a useful candidate. Neither finite-population epigenetic speciation models nor normalized neutral-marker fixation as a barrier measure is new. The searched sources do not establish priority of the exact proposed comparison. The useful result would be a signed epigenetic-versus-genetic comparison, or a precisely delimited counterexample, with common initialization, life-cycle timing, and outcome functional.

## 1. Exact source direction and mathematical object

Planidin et al., *Adaptive epigenetic divergence can facilitate ecological speciation*, [DOI10.1098/rspb.2025.1217](https://doi.org/10.1098/rspb.2025.1217), published 2025-09-17. The authors write in Section 5: “Finite population models may magnify the relative strength of epigenetic barriers to gene flow.” This is a proposed direction, not a universal conjectured inequality.

Their Section 2(b), Eq.(1.1), uses RI=1-Bhat/B0 with B0=m/2: one generation of migrants from deme1 into deme2 is marked BB, and Bhat is the equilibrium neutral-marker frequency. Ordinary migration continues after marking. Primary-contact marking follows equilibration of the selected background; secondary contact uses a different prehistory. Section 4(c) expressly distinguishes their metric and epimutation parameterization from Greenspoon et al. 2022. Section 2(c), Eq.(1.2), already supplies a constant-matrix eigenvector solution for an asexual-haploid approximation. [Primary full text](https://pmc.ncbi.nlm.nih.gov/articles/PMC12440623/).

Reading coverage: full main text had been read in the earlier source audit; Sections 2 and4–5 were rechecked here. The complete 58-page supplement is available locally; pp.3–5 were reread in this task, while the earlier reading covered the spectral derivation/worked example pp.33–38. The remaining supplementary pages have not been comprehensively audited.

The supplement's Section 1.1 specifies 20 phased diploid-adult states across two demes and 8 gamete states, with deme-normalized selection, recombination, gamete formation, random mating and epimutation. Its pp.3–5 are the mathematical reference for an exact stochastic extension. The per-deme normalization and quadratic mating step matter: a finite stochastic mean need not follow the deterministic recurrence exactly.

## 2. Source-code check

The official [Zenodo record 16635603](https://zenodo.org/records/16635603) is dated 2025-07-31 and has no explicit version field. The web wrapper failed, but the ordinary public API was accessible with Python urllib. Seven files were listed. I read the entire README and all 436 lines of `epigen_funcs1.4.cpp`, without executing either. The R orchestration, R helper file, analysis scripts and notebook were not fully read.

The README explains that the implementation has a third locus whose parameters disable its effect in the published analysis. Thus its 72 columns are not a contradiction of the two-locus supplement. `selectionC`, lines 64–93, multiplies frequencies by fitness and normalizes within each deme. `injection_migrationC`, lines 41–61, performs the single-generation BB marking. `RI_calcC`, lines 325–368, computes the two-deme average marker frequency divided by m/2; its deme2-only alternative is equivalent only at equilibrium. `calc_equilibriumC`, lines 374–434, tests consecutive marginal-frequency changes against a tolerance. The C++ engine contains deterministic frequency updates, not finite-population sampling.

Primary file URLs and SHA256:

- [README](https://zenodo.org/api/records/16635603/files/README.md/content): `a454b80f843753af9087d8a75367ccce79d0925c5c233b6d6423fafa48025bfa`.
- [C++ engine](https://zenodo.org/api/records/16635603/files/epigen_funcs1.4.cpp/content): `7ababa60bbc0f56cb7941568d130b6d05c041797ce79c1225c1654782c14da9a`.

The files were read in memory; no source copies were added to this directory.

## 3. Nearest existing results

**Greenspoon, Spencer and M'Gonigle 2022: finite epigenetic speciation already studied.** *Epigenetic induction may speed up or slow down speciation with gene flow*, Evolution76,1170–1182; accepted 2022-03-09, June 2022 issue, [DOI10.1111/evo.14494](https://doi.org/10.1111/evo.14494), [author PDF](https://www.sfu.ca/biology/faculty/M'Gonigle/pdfs/greenspoon-2022-1170.pdf). Methods pp. 1171–1174 describe a stochastic haploid two-patch model, fixed census K=2500, sexual reproduction, freely recombining genetic/epigenetic loci and age-dependent epigenetic resetting. Its main outcome is time to a genetic-bimodality threshold:40,000-generation runs and 35 replicates, with unresolved runs assigned the cutoff for qualitative comparisons. Results pp. 1175–1176 demonstrate sensitivity to survival bottlenecks versus soft selection and to the genotype–epigenotype phenotype map. Discussion p. 1179 identifies drift/bottleneck interaction and recombination robustness as further theoretical questions. These are simulation results and proposed directions, not an exact theorem about Planidin's marker RI. Reading: model, analysis, relevant Results and Discussion in the primary13-page PDF; no comprehensive supplement or code audit.

**Muirhead and Presgraves 2016: the closest finite neutral-marker functional.** *Hybrid Incompatibilities, Local Adaptation, and the Genomic Distribution of Natural Introgression between Species*, American Naturalist187,249–261; online 2015-12-29, February 2016 issue, [DOI10.1086/684583](https://doi.org/10.1086/684583), [author PDF](https://www.zoology.ubc.ca/let/pdfs/Muirhead2015.pdf). Despite the PDF filename, cite the 2016 issue. Models/Eqs.(1)–(8) analyze escape from linked incompatibilities. Simulations pp. 253–254 use a single migration pulse, diploid random mating, selection/recombination, and Wright–Fisher multinomial sampling until the neutral migrant marker fixes or is lost. Barrier permeability is estimated by fixation probability divided by its no-barrier baseline. Their Results p. 254 and Discussion p. 259 report discrepancies when effective recombination is rare (Ne*r much smaller than1), migration fractions are large, or the usual deterministic-selection/adequate-recombination conditions fail. This is direct precedent for finite marker-fate normalization, but it has genetic incompatibilities and a receiving-population pulse model, not Planidin's ongoing symmetric migration plus epimutation. Reading: model assumptions, Simulations/Results and limitations pp. 251–254,258–259; full online appendix not read.

**Smithson, Dybdahl and Nuismer 2019: drift-dependent epigenetic advantages already studied.** *The adaptive value of epigenetic mutation: Limited in large but high in small peripheral populations*, J.Evol.Biol.32,1391–1405, December 2019, [DOI10.1111/jeb.13535](https://doi.org/10.1111/jeb.13535), [PubMed abstract](https://pubmed.ncbi.nlm.nih.gov/31529541/). Mainland–island mathematical models and simulations combine epimutation, migration, selection and drift. The authors report a wider range of adaptive benefits in small peripheral populations. The measured outcome is adaptation, not the exact neutral-marker RI comparison. Reading is abstract-level only; publisher access returned403, so no internal equation or theorem is attributed to the paper here. Planidin cites it as reference 33 and describes its epimutation parameterization as the precursor of the symmetric version used in 2025.

**2025–2026 screening.** Osmanovic, Rabin and Soen, *A Model of Epigenetic Inheritance Accounts for Unexpected Adaptation to Unforeseen Challenges*, published 2025-03-18, Advanced Science12,2414297, [DOI10.1002/advs.202414297](https://doi.org/10.1002/advs.202414297), gives a stochastic/induced-response population model and simplified analytical solutions for changing environments. Abstract/introduction were screened; full technical text was not acquired. It does not, in those inspected passages, address two-deme marker barriers. De Carvalho et al., including Planidin, published *Genomic regions exhibiting divergent DNA methylation patterns co-vary with loci associated with sexual signalling traits in a stick insect* on 2026-07-23, [DOI10.1098/rstb.2025.0024](https://doi.org/10.1098/rstb.2025.0024). The [author-institution record and abstract](https://eprints.whiterose.ac.uk/id/eprint/243859/) describe empirical methylation/signalling associations and a need for causal tests. This is relevant current biological motivation, not a finite-population mathematical solution. No full-paper audit is claimed for this screening item.

## 4. Translation obstructions and exact design choices

The following are our mathematical interpretation checks, not novelty claims or quotations from the papers.

1. **Neutral marker does not imply a martingale under linked selection.** It has no direct fitness effect, but its association with the selected background changes its reproductive contribution. In general E[F(X)] differs from F(E[X]) when selection divides by random mean fitness or reproduction depends nonlinearly on frequencies. Conditional unbiased sampling at the final step does not remove that difference in later generations.

2. **Fixation, eventual expectation and finite-horizon expectation require separate statements.** If the unmutating marker is eventually globally0 or1 almost surely, bounded convergence identifies its limiting expected frequency with fixation probability. That absorption premise must be proved for the chosen kernel, including parameter boundaries and migration connectivity. Finite H only gives E[B_H]; transient survival and genetic fixation are different events. Mutating epialleles can continue changing after the neutral marker absorbs.

3. **Initialization can dominate the finite-size comparison.** A finite closed two-deme genetic model with no selected-locus mutation ordinarily eventually loses or fixes that locus globally when migration and reproduction permit global ancestry and all relevant fitnesses are positive. Infinite burn-in therefore need not preserve deterministic migration–selection polymorphism. An epimutating background may instead have a nondegenerate stationary law. Choose finite burn-in T, a justified quasi-stationary law, or an explicitly stationary comparison. Do not silently identify finite stationarity with the deterministic equilibrium. The limits N->infinity and T->infinity need not commute. In a fixed-size, deme-normalized model, a globally fixed genetic background has no within-deme selective discrimination at the neutral marker; this can make its baseline barrier vanish, a valid but time-scale-dependent comparison requiring explicit proof.

4. **The pulse denominator must be specified.** If migration is sampled, the number k of marked diploid migrants is random and may be 0. With N diploids per deme and k marked BB migrants, total marker frequency is k/(2N). Fixed-k introductions, ratios of expectations, and expectations of ratios conditional on k>0 are distinct. Holding m constant while N changes does not automatically preserve the same realizable pulse.

5. **The selection/reproduction kernel is part of the hypothesis.** End-of-generation multinomial sampling from normalized deterministic frequencies, individual Bernoulli survival followed by population regulation, and random gamete pairing from a finite pool are different finite models. Greenspoon's hard/soft-selection comparison shows why this distinction is scientifically material. In particular, actual viability survival may leave no survivors, requiring an explicit extinction or rescue rule; normalized soft selection avoids that event but changes the model.

6. **A finite-horizon error bound alone does not answer relative magnification.** With a common fixed-pulse denominator, define Delta_N(T,H)=RI_epigenetic,N(T,H)-RI_genetic,N(T,H). The useful result is its sign, a comparison with the deterministic Delta_infinity(T,H), or a parameter-specific reversal. Proving only that both stochastic trajectories approach their deterministic limits leaves this substantive comparison unresolved unless the error is smaller than a proven comparison margin.

## 5. Recommended claim and remaining gates

The defensible candidate is an exact small-N comparison, with common m,s,r, initialization and pulse semantics, showing when adaptive epimutation strengthens or weakens the neutral-marker barrier relative to the mutation-free genetic comparator. A finite-horizon theorem should be labelled accordingly; a fixation theorem additionally needs absorption and control of the tail. A genuinely source-faithful result must preserve phased diploid state, the specified life cycle, and the ongoing migration after the single marker pulse. State any simplified haploid or altered-stage variant separately.

The present investigation does not locate an already published theorem answering that exact comparison, but also does not establish that it is absent. Before a novelty claim, compare the complete Smithson 2019 model, Greenspoon's supplement/code, and older effective-migration/barrier literature. The normalized fixation functional and elementary finite-state calculations themselves should be attributed as established tools. No claim that Planidin predicted a universal finite-size advantage is warranted.

## Search and access record

Eleven focused web queries, without a citation-network census:

1. `Planidin 2025 1217 finite population epigenetic reproductive isolation marker`
2. `epigenetic inheritance reproductive isolation finite population stochastic model 2025 2026`
3. `"epigenetic" "each of fixed population size" patches`
4. `"epigenetic" "reproductive isolation" "2026" model`
5. `"Planidin" "2025" "finite population"`
6. `"effective migration" "fixation probability" "barriers"`
7. `"epigenetic" "barriers" "2025" "2026" finite population model`
8. `"The adaptive value of epigenetic mutation" "small" model`
9. `"16635603" github`
10. `"Adaptive epigenetic divergence" github`
11. `"The adaptive value of epigenetic mutation" pdf Smithson`

Primary follow-ups used article sections, author PDFs, the local Planidin supplement, and the official Zenodo API. PMC sometimes returned a browser challenge; publisher/aggregator wrappers produced403 or internal errors. Ordinary author repositories and the public Zenodo API were used where available, without bypassing access controls. Review/blog/search metadata was not used as evidence of an exact theorem. Other screened hits, including stochastic tumor-resistance models and empirical hybrid studies, were not treated as solutions to this specific ecological comparison.