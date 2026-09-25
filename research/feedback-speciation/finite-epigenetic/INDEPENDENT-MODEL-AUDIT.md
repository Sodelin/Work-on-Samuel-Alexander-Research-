# Independent audit of the finite epigenetic model and exact certificates

Audit date: 2026-09-25. Disposition: **PASS for the source interpretation, exact rational kernels, stored harmonic certificates, and the free-recombination count specialization reviewed below.** This is an independent mathematical and computational audit. No Lean compilation was run by this auditor, and this note does not itself establish a Lean verification receipt.

## Scope and fixed artifacts

The comparison is against [SOURCE-MODEL-CONTRACT.md](SOURCE-MODEL-CONTRACT.md), whose primary-source basis is Planidin et al. (2025), [published article](https://doi.org/10.1098/rspb.2025.1217), [main full text](https://pmc.ncbi.nlm.nih.gov/articles/PMC12440623/), and [official supplement](https://ndownloader.figshare.com/files/57066856), especially pp. 3–5 and 29–30. The source's finite-population suggestion does not assert a universal quantitative inequality. The model here is an explicitly chosen offspring-sampling extension of the published frequency recursions.

Artifacts read and independently checked:

| Artifact | SHA-256 |
|---|---|
| finite_life_cycle.py | 1B852D6DEDD1775EB4733943C9F85AF8CAD09068838BC41120919F7FB6771A78 |
| genetic-exact.json | E8141B99A56DC541FB7DE29E61368C7B4A8175F863A611032411BA306BE96D6E |
| epigenetic-exact.json | 4F8DCB6C5DB29AAB052EB5FCA29BD4522B5A78197972306E41F42068737A0088 |
| count_model.py | 0673BA5E48782D353FB4AF2BC7607A18D36279D9486E5B3A7707D777FC25CC04 |
| count-certificates.json | EC7A8876C02A49A97D9F0CCDECD6FF73C300ADA5E07AFFE90D6DA380D74CF54B |
| SOURCE-MODEL-CONTRACT.md | D0705E105A4ECA313A9B034A466F6F85261CA5DF519E20799D17D7A29ABC3CD8 |

The floating exploration file was not used as mathematical evidence. No proof source, Python source, result JSON, or prior document was edited by this auditor. Independent verification ran as short in-memory Python programs using fractions.Fraction and Python's -B flag; no import bytecode or verifier source files were written. Only this audit note was written.

## Actual 100-state life cycle

The encoding h=2*E+B correctly represents four phased haplotypes, with E and B each zero or one. combinations_with_replacement(range(4),2) gives the ten unordered pairs of homologues. In particular, (0,3) and (1,2) are different double-heterozygote phases. Their distinction survives until recombination. The joint state ordering is the Cartesian product of the two ten-genotype lists, matching the order of the two-deme transition rows.

The implemented fitness is 1-s*wrong/2, with wrong=2-E_count in the first deme and wrong=E_count in the second. These are precisely the source's additive divergent fitnesses. The local adult has pool weight 1-m, and the opposite adult has weight m. The destination-specific weighted fitness sum is normalized before gamete formation. This implements soft selection on a deterministic weighted migrant pool, not random finite migrant counts followed by realized viability survival.

The gamete function assigns weight (1-r)/2 to each parental homologue and r/2 to each recombinant homologue. Duplicated haplotypes accumulate rather than being discarded. This is equivalent to the source's explicit exchange of the two double-heterozygote phases before Mendelian segregation. Independent gamete draws produce one diploid offspring per deme. The two deme offspring are conditionally independent.

Epimutation is applied independently to each paired offspring homologue, flips only the E bit, and reverses alpha and beta between demes. Thus it preserves the neutral marker and its homologue identity. At mu=1/2, phi=1, every next individual in deme 1 has two E copies and every next individual in deme 2 has zero E copies. This reset occurs after the selection and gamete stages; it is not prematurely applied to immigrants before selection.

At N=1, the model allows the same adult to contribute both gametes. There are no distinct-parent or sex constraints. That is consistent with the declared finite lift of random mating, but it must remain explicit when describing biological applicability.

All numbers entering the two exact JSON files are rational: their CLI parameters are fractions, the computations use Fraction throughout, and harmonic verification uses equality, not a floating tolerance. The existence of a separate floating exploration mode does not weaken the exact-mode outputs audited here.

## Introduction pulse and interpretation of fixation

The implemented initial state is EEbb in deme 1 and eebb in deme 2. In the first step only, the migrant contribution from deme 1 into deme 2 is changed to BB while preserving E/e. The opposite migrant contribution remains unmarked. Subsequent rows use ordinary migration without further introduction. This agrees with the source's directional neutral-marker pulse and the chosen matched secondary-contact backgrounds.

The initial global marker dose is m/2 in the weighted-pool convention. For the stored results m=1/4, so B0=1/8. The computed fixation probability is the pulse distribution dotted with the ordinary-kernel fixation function. The RI calculation 1-P_fix/(m/2), equivalently 1-8*P_fix for these parameters, uses that global denominator correctly. It does not mix the main article's global units with the supplement's recipient-only m normalization.

Nine full-genotype states have no B copies and nine have only B copies. These are absorbing marker classes, leaving 82 mixed states. The epigenetic selected locus may continue changing inside a marker boundary, so describing all boundary states as individually absorbing would be inaccurate. The code correctly sets their fixation values without requiring their full genotypes to remain fixed.

The stored solution is harmonic on all 100 states, equals zero on the B-free class, equals one on the B-fixed class, and lies in [0,1]. Those equalities alone should be accompanied by an absorption argument. The independently checked kernels have positive one-step probability of reaching each marker boundary from every mixed state. The state space is finite, so there is a uniform positive escape probability and absorption occurs almost surely. This validates the eventual-marker-fixation interpretation and uniqueness of the bounded harmonic solution. No general martingale assertion about the genetic global-marker process is needed or justified.

## Independent full-kernel verification

The independent verifier did not reuse finite_life_cycle.py's functions. It implemented recombination by exchanging the two double-heterozygote genotype frequencies, then performed segregation. For the last mutation stage it used the mathematically equivalent operation of independently mutating the two gamete laws before pairing. This alternative is valid because the two mutation events are independent and pairing introduces no selection; it does not move mutation before viability selection.

For each of the two parameter sets, the verifier checked:

- All 10,000 stored transition entries against the independently generated kernel.
- Nonnegativity and unit mass of each of the 100 rows.
- All 100 entries of the direction-specific pulse distribution.
- The 9+9 marker boundary states and all 82 mixed states.
- All 100 exact harmonic equations and the boundary values of the stored certificate.
- Positive probability of reaching each marker boundary from every mixed row.
- The exact pulse-weighted fixation probability and its reported RI normalization.

Both runs passed. These were exact enumerations, not Monte Carlo simulations or approximate matrix solves. The audited values are:

| Model, with m=1/4 and s=r=1/2 | mu | P_fix | RI_fix |
|---|---:|---:|---:|
| Mendelian selected locus | 0 | 323808055/4466354606 | 937945083/2233177303 |
| Pure adaptive induction, phi=1 | 1/2 | 1/14 | 3/7 |

Therefore, in this finite model and at these specific parameters,

    RI_fix(epigenetic) - RI_fix(genetic)
      = 19130904/2233177303 > 0.

The pure-induction value also agrees with the already published boundary formula s*(1-m)/(1-ms). This is an independent source benchmark, not a claim that the formula was newly discovered.

## Free-recombination count specialization

count_model.py is specialized to m=1/4, s=r=1/2. With r=1/2, a parent's selected and neutral alleles are independently sampled for its gamete: the gamete law depends only on the two allele counts, not linkage phase. This justifies adult encoding g=3*E_count+B_count in {0,...,8}, and joint encoding x=9*g0+g1 in {0,...,80}. At other recombination rates the phase quotient is generally invalid; the 100-state model retains the phase needed for those cases.

The integer fitness scores 2+E_count and 4-E_count equal four times the corresponding viability fitnesses. Migration weights 3 and 1 encode the 3/4 local, 1/4 immigrant mixture. If w0 and w1 are these migration-weighted fitness scores, each gamete numerator combines the relevant E-copy and B-copy counts, and the denominator is 4*(w0+w1). The factors of four come from independently choosing an allele from each pair of homologues at free recombination. No genotype-fitness normalization is omitted.

The non-epigenetic nine-entry offspring polynomial sums the sixteen ordered gamete-pair contributions into the nine possible pairs of allele counts. Its central term 2*u*z+2*v*w correctly combines the two distinct double-heterozygote phases. For pure induction, the marker-count binomial weights are retained while the next E count is forced to two in deme 1 and zero in deme 2. The parent gamete pool was already calculated from pre-reset E counts, so this operation implements the final epimutation stage correctly.

An independent integer enumerator reconstructed each offspring polynomial by explicitly enumerating all sixteen ordered gamete pairs and only afterward applying the epigenetic E-count reset. It verified all 81 integer rows for each model, then independently rechecked their aggregation against every phased row of the already validated 100-state kernels. It also checked the pulse, certificate numerators, denominators, boundary values, and exact integer harmonic identities.

Results:

| Check | Genetic | Epigenetic |
|---|---:|---:|
| Full phased rows rechecked under aggregation | 100 | 100 |
| Integer count rows independently enumerated | 81 | 81 |
| Integer harmonic identities checked | 81 | 81 |
| Common certificate denominator | 3720412 | 8580 |
| Minimum one-step probability of either marker boundary | 72/2401 | 72/2401 |

The initial count-state index is 54: g0=6 denotes EEbb and g1=0 denotes eebb. The pulse vectors agree exactly under phase aggregation, and their weighted certificates reproduce the full-model fixation probabilities. The minimum terminal mass 72/2401 is strictly larger than the advertised uniform bound 1/100.

The pure-induction kernel is defined on all 81 count states, even though after a reset only nine of them remain possible. A certificate denominator larger than four is therefore not evidence against the simple post-reset global-frequency martingale; arbitrary pre-reset states still undergo a selection step before entering that smaller invariant set.

## Independent two-generation comparison at different parameters

The source-contract note proposed a separate small test with N=1, m=s=1/2, r=0. This is not the parameter set of the two fixation JSON files. Here the first genetic offspring have independent counts

    A ~ Binomial(2,2/3), K ~ Binomial(2,1/3),

where the source is unmarked and the recipient's K selected E copies also carry its K B copies. Both models have first-step global marker expectation 1/6. Direct destination-specific selection in the next step gives

    E[Q2 | A,K]
      = (1/4)*((2*K+K^2)/(4+A+K)
               +(4*K-K^2)/(8-A-K)).

The independently re-evaluated nine-state sum is exactly 317/1890. A second verification generated the full phase-aware pulse and one ordinary transition step using the independent kernel implementation; it gave the same result. The pure-induction calculation gave 1/6 for both first and second steps.

Thus the hand calculation is now independently confirmed by exact rational computation:

    E_genetic[Q2] = 317/1890,
    E_epigenetic[Q2] = 1/6,
    E_genetic[Q2] - E_epigenetic[Q2] = 1/945,
    RI2(epigenetic) - RI2(genetic) = 4/945.

This verifies a finite-horizon subsequent-selection effect and the first-step equality control. It does not identify either model's eventual fixation probability at m=1/2,r=0.

## What this establishes and what remains separate

There is no material source-model or arithmetic defect in the reviewed artifacts. The exact comparisons concern neutral migrant-marker transmission and fixation in the stated two-deme finite model, with drift introduced at offspring sampling. They do not classify biological species, establish organism-ancestry IAP, model learned culture, or demonstrate an empirical epigenetic mechanism in nature.

Three evidence levels must remain distinct:

1. **Source and mathematical fidelity:** established here by comparing definitions and order with the source contract and reviewing the absorption and phase-aggregation arguments.
2. **Exact rational computation:** independently checked here for both full kernels, both harmonic certificates, both count specializations, and the two-generation example.
3. **Lean verification:** not performed or certified by this audit. The implementation lane's eventual Lean source, theorem statements, imports and successful receipt must be assessed on their own terms.

The positive finite-model RI difference is not, by itself, proof that finite population size amplifies the relative epigenetic barrier compared with the infinite-population model. That stronger claim requires a matched infinite-population baseline, the same contact protocol and observable, and a validated comparison to that baseline. Neither a universally stronger epigenetic barrier nor population-size monotonicity follows from this one finite parameter setting. Novelty remains a separate literature question.