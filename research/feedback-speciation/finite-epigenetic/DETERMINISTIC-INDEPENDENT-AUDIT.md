# Independent audit of the deterministic comparison

Date: 2026-09-25. Disposition: **PASS for the written mathematical reduction, the common-limit proof, and the stated draft Lean correspondence.** Exact rational prefix and coefficient checks also passed independently. This auditor did not compile Lean. The reviewed Lean source is a draft whose actual statement scope is narrower than the complete written argument.

Only this audit note was written. No proof source, Python source, or existing document was edited. The four-generation exact calculations below used an in-memory Fraction verifier, not floating-point diagnostics or a long simulation.

## Exact reviewed versions

| Artifact | SHA-256 |
|---|---|
| DETERMINISTIC-COMPARISON.md | 5D4128D6023FF4559EEB649D72EA62AD581E30026C75268FBDADEF929931B773 |
| deterministic_comparison.py | 53302A86D2BB5074421A3C11742508BE3CF7176F1CF3030969C7A22688043DBD |
| DeterministicEpigenetic.lean | E6570B42CB691C802553BE9315D14D936A1FE8908C2F590D66BFC0E7DDE07F69 |
| FINITE-RESULT.md | 2A737D11520C0D4A383E0526C96294E429518212062DC373E973D14A640B5D8A |

The biological source remains Planidin et al. (2025), [main article](https://pmc.ncbi.nlm.nih.gov/articles/PMC12440623/) and [official supplement](https://ndownloader.figshare.com/files/57066856), particularly its diploid recursion on pp. 3–5. The finite model's separate source audit is [INDEPENDENT-MODEL-AUDIT.md](INDEPENDENT-MODEL-AUDIT.md).

## 1. The full source model really admits this conditional reduction

The deterministic population consists of two distributions over ten phased diploid genotypes, hence twenty genotype frequencies. It is not a probability distribution on the 100 two-adult states used in the finite model. The script updates the deterministic genotype frequencies directly.

For the genetic case mu=0, every completed generation is a random pairing of the four haplotype frequencies. This is Hardy–Weinberg pairing of homologues, not an assumption of independence between the selected and neutral loci on one homologue. Linkage disequilibrium is retained in the four haplotype frequencies.

Whole-adult migration makes a mixture of the two source distributions. That mixture need not itself be Hardy–Weinberg. The written derivation correctly keeps the source-deme index through viability selection. It does not replace the migrated mixture by random pairing before selection.

At r=1/2, the homologue supplying the selected allele and the homologue supplying the neutral allele are independent uniform choices within the same adult. They coincide with probability one half. For a source deme l and destination selected allele b, conditioning the marker on source selected allele a therefore gives the two unnormalized contributions

    N[(d,b),(l,a)] = (lambda[d,l]/2) *
      ( 1[a=b] * P_l(a) * sum_c P_l(c)*w_d(a,c)
        + P_l(a)*P_l(b)*w_d(a,b) ).

The first term is the same-homologue contribution; the second is the different-homologue contribution. The latter factors across homologues because the source adult was formed by random mating. This is the appropriate place to use Hardy–Weinberg pairing.

Summing N over l,a gives the unnormalized selected-gamete mass W_d*P'_d(b). Consequently A=N/(W_d*P'_d(b)) is nonnegative and row stochastic. Its application to the four conditional marker frequencies is exactly the full source update, not an assumed temporal mixing law.

At symmetric selected background p in deme 1 and 1-p in deme 2, and m=1/4,s=1/2, the first two rows have unnormalized coefficients u/32 and v/32, where

    u = (3(1-p)(4-p), 9p(1-p), p(3+p), 3p(1-p)),
    v = (9p(1-p), 3p(3+5p), 3p(1-p), (1-p)(8-5p)).

The other rows are reverse(v)/32 and reverse(u)/32. For example, the first same-background coefficient is

    (3/8)*((1-p)*(2+p)/4 + (1-p)^2/2)
      = 3(1-p)(4-p)/32.

This makes the scale factor and the normalization explicit. The normalized row sums are the documented 12-8p^2 and 8+8p+8p^2; the factor 32 cancels.

I independently evaluated every one of the sixteen unnormalized coefficient identities at p=0,1/2,1. Both sides have polynomial degree at most two, as is explicit from their products of selected marginals and affine expected fitness. Equality at these three distinct values therefore verifies the polynomial identities, not merely agreement along three trajectory states. This supplements the direct algebraic derivation.

## 2. Background symmetry and the postpulse index are correct

At the marked first migration, deme 1 has selected parental weights 3/4 for EE and 1/8 for ee, giving E frequency 6/7 in its gametes. Both contributions there remain unmarked. In deme 2, local ee has weight 3/4 and the marked migrant EEBB contribution has weight 1/8. Its E frequency is 1/7, with every E homologue carrying B and every e homologue carrying b.

Thus after the entire first mating step,

    p1 = 6/7,
    theta1 = (q1e,q1E,q2e,q2E) = (0,0,0,1).

Random mating preserves these haplotype marginals and places both demes in the pairing form needed for the next reduced step. The neutral marker cannot affect the selected-locus recurrence because viability depends only on selected genotype. Swapping the demes and complementing E/e preserves that recurrence, so the selected marginals remain p and 1-p despite the asymmetric marker pulse.

The Lean trajectory index zero is this biological generation one. Consequently trajectory 3 is biological generation four. The written proof, Python exact prefix and Lean draft use the same offset. The finite initial dose remains m/2=1/8; the postpulse mean 1/14 is not substituted for it in the RI denominator.

The selected-gamete masses give

    p' = (2+2p+2p^2)/(5+2p),
    p'-2/3 = (p-2/3)*2(p+1)/(5+2p).

On [2/3,6/7], the multiplier is positive and at most 26/47<1. This explicit uniform bound strengthens the written monotonicity explanation: p remains in the interval and tends geometrically to 2/3. The common-marker-limit argument below actually needs only interval invariance.

## 3. The 1/784 bound and common-limit proof are valid

For every source selected background, P_l(a)>=1/7 throughout the invariant interval. The same holds for P_l(b). Also lambda[d,l]>=1/4 and w_d(a,b)>=1/2. Destination mean fitness W_d and next selected marginal P'_d(b) are positive and at most one. The different-homologue term alone yields

    A[(d,b),(l,a)]
      >= lambda[d,l]*P_l(a)*P_l(b)*w_d(a,b)/(2*W_d*P'_d(b))
      >= (1/4)*(1/7)^2*(1/2)/2
      = 1/784.

The direction of the denominator bound is correct. All sixteen entries satisfy it, including off-deme and off-selected-background entries. No irreducibility assertion is being inferred merely from positive migration.

For epsilon=1/784, write each stochastic row as its common epsilon contribution plus a nonnegative residual row of mass 1-4*epsilon. The epsilon times sum(theta) term is identical across the four output coordinates. Therefore

    range(theta') <= (1-4/784)*range(theta)
                  = (195/196)*range(theta).

Convex averaging also makes the minimum nondecreasing and maximum nonincreasing. They are bounded by the initial interval [0,1], so both converge as real sequences. Their difference tends to zero by the displayed geometric estimate, forcing a common limit c. Every conditional marker coordinate is squeezed between them. Both actual deme marker means are convex combinations of those four coordinates, so they also converge to c. Convergence of the weights themselves is not needed for this final squeezing step.

This is a valid written existence proof of the common deterministic marker limit. It is not a numerical stopping criterion. The 195/196 factor is coarse but strictly smaller than one.

## 4. Independent exact verification of the four-generation certificate

A separate full-genotype implementation was used in memory. It kept all ten phased genotypes in each deme, mixed adult distributions, applied destination viability, explicitly exchanged double-heterozygote phase at free recombination, performed segregation, and randomly paired gametes. It did not call deterministic_comparison.py's functions.

At each of biological generations 1,2,3,4, its extracted selected marginal and four conditional marker frequencies agreed exactly with the reduced recurrence. The fourth-generation values are

    p4 = 2255346713174/3234958787249,

    theta4 = (
      158042799831/2612298864200,
      825778109695/18042773705392,
      1228259142369/18042773705392,
      172444392929/2612298864200 ).

Their maximum is

    M = 1228259142369/18042773705392 < 1/14.

The convex-range invariant therefore bounds every subsequent conditional coordinate, both marker means, and their common limit by M. Exact rational arithmetic independently verified

    RI_genetic >= 1-8M
               = 1027087570805/2255346713174,

    (1-8M)-3/7 = 423572856113/15787426992218 > 0.

This proves the deterministic sign without relying on the reported numerical limit 0.53156909.... Pure induction has postpulse means (0,1/7), preserves their sum 1/7, and contracts their difference by 5/7. Hence its actual common limit is 1/14 and its RI is exactly 3/7. The deterministic genetic barrier is therefore strictly stronger in this matched experiment.

## 5. What the draft Lean source actually states

The mathematical statement audit of DeterministicEpigenetic.lean passes, subject to compilation by the owning lane. It defines the displayed reduced recurrence directly. There is no Lean definition of the twenty-frequency source model or theorem transporting that source trajectory into this reduction.

| Draft declaration | Actual scope |
|---|---|
| background_from_rows | Algebraic relation between the declared row sums and the declared scalar background map. It is not the source-to-reduction theorem. |
| background_invariant; trajectory_background | The declared scalar trajectory stays in [2/3,6/7]. |
| row_positive; marker_box_invariant | Positive weighted averaging preserves a common nonnegative upper bound. |
| generation_four_exact; generation_four_background_exact | Exact fourth biological generation of the reduced trajectory, whose index is 3. |
| all_later_marker_box; all_later_mean_bound | Upper bounds at every finite index n+3 of the reduced trajectory. |
| deterministic_genetic_tail_bound | The exact strict RI inequality at every such finite index. |
| limiting_mean_bound; limiting_genetic_RI_bound | Bounds for a supplied L satisfying the explicit MeanConverges L premise. They do not prove such an L exists. |
| induction_sum_constant; pure_induction_RI_exact | The induction sum and its finite-time mean-based RI are exact. They do not themselves prove convergence of the deme difference. |
| deterministic_ranking_strict | Strict comparison of the two declared finite-time RI sequences at every index n+3. It is not an unconditional common-limit comparison theorem. |

The reviewed draft contains neither a theorem asserting existence of a common genetic limit nor the uniform-entry/range-contraction proof. It also does not establish source Hardy–Weinberg preservation or all-generation equivalence with the full twenty-frequency recursion inside Lean. Those are genuinely completed written mathematics in the current packet, supported by the independent derivation above, but remain outside this draft's formal scope.

The conditional limit premise is explicit and appropriate; it is not a hidden assumption. Future reporting should retain that distinction even after the draft successfully compiles. Compilation will check the proofs of the stated reduced-model results, not automatically expand their scope.

## 6. Document claims and reporting disposition

No material overclaim was found in the exact reviewed DETERMINISTIC-COMPARISON.md. It explicitly labels its source correspondence, invariance and convergence argument as written mathematics, labels the exact prefix as Fraction arithmetic, and says it is not a Lean verification receipt. Its numerical approximation is expressly not a certified decimal enclosure. The ranking-reversal conclusion is justified as a written theorem together with the separately verified finite comparison.

FINITE-RESULT.md correctly says that the deterministic comparison is under formalization and distinguishes the finite count formulas checked in Lean from the audited phase reduction. This audit did not rerun or independently re-audit its earlier finite compiler receipt.

One wording precision is useful when presenting this result: conditional on a finite census x, the chosen offspring-sampling kernel does have conditional mean equal to the source update F(x). What generally differs is the unconditional finite mean trajectory E[F(X)], which is not F(E[X]). The deterministic note's warning about expectation and normalization should be read in this latter sense; there is no inconsistency in its actual deterministic implementation.

The new result is a **parameter-specific ranking reversal**: genetic exceeds pure induction in the deterministic model, while pure induction exceeds genetic in the selected finite N=1 extension. It should not be described as merely magnifying an already positive deterministic epigenetic advantage at these parameters. Nor does it prove a monotone relationship in N, a universal epigenetic advantage, an empirical speciation claim, or novelty across the literature.

Safe current status: written proof and independent exact correspondence checks passed; the draft Lean statements faithfully capture the reduced finite-tail and conditional-limit claims; compilation, common-limit existence in Lean, and a full-source-to-reduced Lean theorem are separate remaining formal gates. No proof expansion was made by this auditor.

## Verification addendum, 2026-09-25

Historical draft/audit statements above are preserved. The [combined receipt](verification/combined-receipt.json) records 34 selected endpoints across FiniteFixation, FiniteEpigenetic, DeterministicEpigenetic and RankingReversal. The final deterministic source hash is ece655b0af42fbd580ca86b3f8176a8b4323fe3fd716da9429f13f6366f3117f. Changes after its reviewed draft repaired proof syntax/status text without changing the recurrence or mathematical statements. Reports use only propext, Classical.choice and Quot.sound. RankingReversal imported the preserved deterministic object and exited zero; the earlier deterministic process exit remains unretrieved and explicitly null. This addendum does not extend formal scope to source transport or deterministic common-limit existence.
