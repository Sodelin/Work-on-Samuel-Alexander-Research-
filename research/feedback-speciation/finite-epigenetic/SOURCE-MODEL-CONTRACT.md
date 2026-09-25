# Finite epigenetic model: source contract and exact benchmarks

Date: 2026-09-25. Status: independent source and mathematical design audit. This note does not report a Lean check, simulation, numerical approximation, or completed fixation calculation for the comparative genetic model. It specifies the model and provides hand-derived exact checks for the implementation lane. Only this new note is owned by this audit; the earlier package remains untouched.

## Source and reading scope

Planidin, de Carvalho, Feder, Gompert, House and Nosil, *Adaptive epigenetic divergence can facilitate ecological speciation*, Proceedings B 292, 20251217, published 2025-09-17. [Published article](https://doi.org/10.1098/rspb.2025.1217); [full main text at PMC](https://pmc.ncbi.nlm.nih.gov/articles/PMC12440623/); [official supplementary PDF](https://ndownloader.figshare.com/files/57066856); [Figshare metadata](https://api.figshare.com/v2/articles/29875972); [source code archive](https://doi.org/10.5281/zenodo.16635603).

The current audit read the actual main-text model, marker definition, results and conclusion, and the supplement's exact recursions on pp. 3–5 and no-inheritance calculation on pp. 29–30. Earlier reading also covered its constant-matrix haploid calculation on pp. 33–38. This does not claim an audit of every page of the 58-page supplement or execution of the source code. The local supplement was already available in the research collection; no new large download was needed.

The authors propose investigating whether finite populations can increase the relative barrier attributable to epigenetics. They do not state a universal inequality valid for every finite migration rule, initial condition, parameter choice and isolation statistic. Their existing results already vary with migration, inheritance, induction and contact history. Our finite model and theorem must therefore be stated as a chosen extension of their equations, with its own precise observable. [Main article, conclusion §5 and Methods §2](https://pmc.ncbi.nlm.nih.gov/articles/PMC12440623/).

## Exact biological state and life-cycle contract

The source has two demes, diploids, one selected E/e locus and one linked neutral B/b locus. For an individual with j copies of E, j in {0,1,2}, destination fitness is

    w1(j) = 1 - s + s*j/2,
    w2(j) = 1 - s*j/2.

The ten unordered pairs of the four haplotypes EB, Eb, eB, eb are the ten phased diploid genotypes per deme. The two double heterozygotes EB/eb and Eb/eB must be distinguished. Recording only the two allele counts loses the recombination-relevant phase. Thus one diploid per deme gives exactly 10*10 = 100 joint census states. [Supplement, §1.1, pp. 3–4](https://ndownloader.figshare.com/files/57066856).

One complete step must follow this order:

1. Mix the two adult genotype-frequency pools with weights 1-m and m, reversing source and destination for the other deme.
2. Multiply each genotype's weight by its destination-specific fitness and normalize separately within each deme.
3. Apply recombination at rate r, then form gametes by ordinary Mendelian segregation.
4. Independently draw two gametes for each offspring and pair them.
5. Apply independent epimutation to each offspring homologue, changing only E/e and preserving its linked B/b allele.
6. Record the finite offspring census. Equivalently, sample offspring from the full post-epimutation genotype distribution.

Steps 1–5 reproduce the source's order; the finite sampling in step 6 is the extension. A direct implementation can draw gametes and mutation outcomes, or calculate their exact joint offspring distribution and sample it. These have the same law. Independent epimutation after pairing can also be moved to the two independently sampled gametes without changing this particular offspring law. That observation does not allow moving epimutation to before selection. [Supplement, §1.1.1–1.1.7, pp. 3–5](https://ndownloader.figshare.com/files/57066856).

Epimutation uses alpha=mu*(1+phi), beta=mu*(1-phi). In deme 1, e changes to E with probability alpha and E changes to e with probability beta; the rates reverse in deme 2. The chosen admissible parameter range is 0<=mu<=1/2 and -1<=phi<=1, ensuring both are probabilities. For the two compared endpoints, mu=0 is the source's Mendelian genetic model, and mu=1/2, phi=1 resets every offspring to EE in deme 1 and ee in deme 2. No injective individual labels, ancestry graph, learned behaviour or culture variable is present in this model.

For the finite comparison, use 0<m<1, 0<=s<1, 0<=r<=1/2. Positive minimum fitness avoids a zero normalization denominator. Any theorem admitting s=1 needs a separate convention and analysis of pools containing only zero-fitness genotypes.

## Which finite lift is being certified

The recommended and currently proposed lift is a fixed-size, soft-selection offspring-sampling model. Each deme contains N>=1 diploids. The actual empirical genotype frequencies determine a weighted migrant pool, selection is normalized on that pool, and each deme's N offspring are independent draws from its resulting offspring distribution. Offspring draws in the two demes are conditionally independent.

Consequently, conditional on the current census x, the expected next genotype frequencies are exactly the source recursion F(x). In general, E[F(X)] is not F(E[X]); nonlinear selection normalization makes this distinction substantive. This finite process is not asserted to have the same unconditional mean trajectory as the infinite-population recursion.

The migration stage uses weighted reproductive pools, not a random integer census of migrants followed by realized viability survival. A model that first samples how many adults migrate and then normalizes selection on that realized pool can have different expectations, because an expectation of a ratio generally differs from a ratio of expectations. Both are conceivable biological models; only the first is specified here.

Random mating is sampling with replacement. It permits the same adult to supply both gametes and permits parental reuse among offspring. In the N=1 benchmark this selfing allowance is particularly visible. The model does not require two distinct biological parents, separate sexes, mate choice, a pedigree census with literal emigrants, or a finite-population allopatric burn-in. It is a deliberately small exact counterpart of the frequency equations, not a claim that one diploid per deme is a representative natural population.

## Matched secondary-contact introduction and normalization

Use the same initial census for both models: every deme-1 adult is EEbb and every deme-2 adult is eebb. These locally fixed states are allopatric equilibria for both mu=0 and mu=1/2, phi=1. During the first migration stage only, convert the 1-to-2 migrant contribution to BB, without altering its selected locus. Keep the opposite migrant contribution unmarked. All later steps use ordinary, unmarked migration.

This is the source's direction-specific marker pulse, applied to the chosen weighted-pool finite model. The initial global marker dose is B0=m/2: the recipient migrant fraction is m and the demes have equal size. A literal random number of marked migrants would give a random initial dose and requires an explicitly different normalization or conditioning convention.

The main article uses global marker frequency B0=m/2. Supplement p. 30 writes the no-inheritance calculation in recipient-normalized units B0=m. Both numerator and denominator are rescaled by two, giving the same RI. Do not compare a global numerator to a recipient-only denominator. [Main article §2(b)](https://pmc.ncbi.nlm.nih.gov/articles/PMC12440623/); [supplement §2.2.1, p. 30](https://ndownloader.figshare.com/files/57066856).

For a finite process there are several distinct observables:

- Q_t: realized global B frequency after the t-th complete offspring step.
- E[Q_t]: expected marker transmission at a specified finite horizon.
- P_fix: probability that B eventually fixes across both demes.
- RI_t = 1-E[Q_t]/(m/2), a finite-horizon statistic defined for this extension.
- RI_fix = 1-P_fix/(m/2), the corresponding fixation-probability statistic.

The source's deterministic eventual common frequency is not literally a random finite census limit. Equating lim E[Q_t] with P_fix requires marker absorption. Neither RI_t nor RI_fix alone defines a species or Alexander's IAP property.

## First source-order control: immediate marker equality

For identical current phased genotype frequencies, migration parameters, selection parameters and recombination parameters, changing only the last epimutation stage does not change the one-step distribution of the offspring B-copy counts. Epimutation leaves B/b untouched. Thus the genetic and pure-induction models have identical E[Q_1] under the matched introduction above.

This is a useful check against an incorrect life-cycle implementation. A claimed immediate neutral-marker advantage from changing mu alone, while retaining the same preselection state, would contradict this specified order. A genuine comparison can emerge after the resulting different E/e states encounter a later selection stage, or when deliberately comparing different pre-contact backgrounds.

## Pure-induction finite benchmark and absorption argument

Take mu=1/2, phi=1. At each post-epimutation census, deme 1 is entirely EE and deme 2 entirely ee. Let q1,q2 be their B frequencies, and put

    a = m*(1-s)/(1-m*s).

The selected resident weight is 1-m and the immigrant weight is m*(1-s), with total 1-m*s. The next gamete B probabilities are therefore

    p1 = (1-a)*q1 + a*q2,
    p2 = a*q1 + (1-a)*q2.

For N diploids per deme, the next B-copy counts are conditionally independent Binomial(2N,p1) and Binomial(2N,p2). Recombination does not affect these marginal probabilities. Therefore Q=(K1+K2)/(4N) is a bounded martingale after the initial reset.

For 0<m<1 and 0<=s<1, we have 0<a<1. In every mixed global-marker state, both p1 and p2 lie strictly between zero and one. Thus there is positive probability of producing only B copies in both demes in one step, and positive probability of producing only b copies. The count state space is finite. A positive uniform lower bound on the absorption probability follows, and the chance of avoiding absorption for k steps tends to zero geometrically. Hence marker absorption occurs almost surely. Bounded convergence applied to the martingale gives P_fix=E[Q_initial].

During the one-way marked pulse, the recipient postselection B probability is a and the other deme's is zero. Thus E[Q_1]=a/2, and the reset makes the subsequent martingale calculation applicable. The finite fixation statistic is exactly

    P_fix = a/2,
    RI_fix = 1-a/m = s*(1-m)/(1-m*s).

For m=s=1/2, this gives a=1/3, B0=1/4, P_fix=1/6 and RI_fix=1/3, for every positive N in this particular offspring-sampling lift.

The RI formula is already explicitly given in supplement Eq. (20), p. 30, at phi=1. Its recovery is a source benchmark, not a newly discovered formula. The finite absorption/martingale argument explains why offspring drift does not change this boundary-case answer in the chosen extension. It does not establish the relative finite-population genetic comparison. [Supplement §2.2, pp. 29–30](https://ndownloader.figshare.com/files/57066856).

## General marker absorption also supports the 100-state genetic calculation

The full selected genotype process need not have absorbing individual states when epimutation continues. Marker-free and marker-fixed sets of states are nevertheless absorbing classes, since neither recombination nor epimutation creates a missing neutral allele.

Under 0<m<1 and 0<=s<1, a global B carrier contributes positively to each destination's selected migrant pool. If at least one B copy exists among the 4N copies, every destination gamete has B probability at least

    c = min(m,1-m)*(1-s)/(2N) > 0.

The same bound holds for b whenever a b copy exists. This follows by selecting a carrier adult's contribution, using minimum fitness 1-s, noting that the normalization denominator is at most one, and using its marginal probability of transmitting the relevant neutral allele, at least 1/2. Recombination preserves that marginal probability.

Thus from every mixed marker state the probability of all-B offspring is at least c^(4N), and that of all-b offspring is at least c^(4N). These events are disjoint. The chance of remaining mixed for k more generations is at most (1-2*c^(4N))^k. Marker absorption therefore holds for both the genetic and epigenetic finite models, independently of any martingale claim for the full genetic process.

For an exact finite matrix P, a function f with value 0 on marker-free states, value 1 on marker-fixed states, and f(x)=sum_y P(x,y)*f(y) on mixed states can consequently be identified with the actual fixation probability. Solving those harmonic equations is not enough by itself if the boundary/absorption argument is omitted. Here the structural bound supplies that missing condition. The genetic process generally does not make global marker frequency a martingale.

## A small nontrivial comparative target: two complete steps

The following is a hand-derived exact target, not yet a machine-checked result in this note. It is a finite-horizon comparison and must not be relabelled an eventual-fixation result.

Set N=1, m=s=1/2, r=0, use the matched introduction above, and compare mu=0 against mu=1/2, phi=1. After the first genetic offspring step, write A for the source individual's E-copy count and K for the recipient individual's E-copy count. Then:

    P(A=0,1,2) = (1,4,4)/9,
    P(K=0,1,2) = (4,4,1)/9,

independently. The source is unmarked. In the recipient each E homologue carries B, so its B-copy count is also K. Both models have E[Q_1]=1/6.

For the second genetic step, migration at m=1/2 puts equal weights on these two adult genotypes in both destination pools. With H=A+K, the two fitness denominators are (4+H)/4 and (8-H)/4. Their selected marker probabilities give

    E[Q_2 | A,K]
      = (1/4)*((2*K+K^2)/(4+A+K)
               + (4*K-K^2)/(8-A-K)).

For K=0 this is zero. The three values for A=0,1,2 when K=1 are (9/35,1/4,9/35); when K=2 they are (1/2,17/35,1/2). Weighting by the nine product probabilities gives

    E_genetic[Q_2]
      = (4/81)*(9/35+4*(1/4)+4*(9/35))
        + (1/81)*(1/2+4*(17/35)+4*(1/2))
      = 64/567 + 311/5670
      = 317/1890.

The pure-induction process has E_epigenetic[Q_2]=1/6=315/1890 by the preceding martingale identity. Therefore

    E_genetic[Q_2] - E_epigenetic[Q_2] = 1/945,
    RI_2(epigenetic) - RI_2(genetic) = 4/945 > 0.

This calculation tests a genuine subsequent-selection effect in the finite model, while the first-step equality tests life-cycle fidelity. It uses only nine first-step states and exact rational arithmetic, so it is a modest independently checkable target alongside a larger 100-state fixation certificate. A successful certification would establish this parameter-specific finite-horizon comparison, not a universal epigenetic advantage or a population-size monotonicity theorem.

## Stopping boundary and useful handoff

The source-faithfulness disposition is: the proposed 100-state N=1 process is an acceptable explicit finite offspring-sampling extension of the published recursions, provided phase, destination normalization, pulse direction, independence, selfing allowance and final epimutation timing remain as specified here.

The minimal useful package is the exact kernel with probability preservation, first-step marker equality, the pure-induction scalar benchmark, and a verified rational comparison. A full genetic fixation calculation should identify its harmonic certificate with actual absorption probabilities. Comparing those values addresses one concrete instance of the authors' finite-population direction. It does not establish novelty, solve every parameter regime, prove that finite size always magnifies the relative effect, or connect this neutral-marker statistic directly to biological species boundaries or organism-ancestry IAP.

No Lean source was edited or compiled by this audit, no simulations were run, and no author was contacted. Formal status and any later numerical or certificate results belong to the implementation receipt, not to this source-contract note.