# Deterministic comparison for the matched finite epigenetic example

Date: 2026-09-25. Scope: one matched parameter choice and one explicitly chosen finite sampling model. This note contains a written mathematical proof and exact rational computations; it is not a Lean verification receipt. Decimal values below are numerical convergence diagnostics, with no certified error enclosure for their printed digits.

The comparison reverses the ranking. In the deterministic source model the genetic barrier is stronger. In the finite model with one sampled diploid offspring per deme the epigenetic barrier is stronger. The finite result therefore does not amplify an already positive deterministic epigenetic advantage at these parameters.

| Model | Genetic marker RI | Pure-induction marker RI | Epigenetic minus genetic RI |
|---|---:|---:|---:|
| Deterministic, infinite population | approximately 0.531569093028565 | exactly 3/7 = 0.428571428571429 | approximately −0.102997664457136 |
| Finite, N = 1 per deme | 937945083/2233177303 = 0.420004753648528… | exactly 3/7 | 19130904/2233177303 = 0.008566674922900199… |

The finite row is taken from the separately checked local `genetic-exact.json` and `epigenetic-exact.json` artifacts. This comparison independently computes the deterministic row; it does not re-prove the finite transition system. The difference between the two signed advantages is numerically about 0.111564339380037.

## Source and common experiment

The source is [Planidin et al. (2025), DOI 10.1098/rspb.2025.1217](https://pmc.ncbi.nlm.nih.gov/articles/PMC12440623/), particularly Methods §2(a), the pulse-marker definition in §2(b), and electronic supplement §1.1, pp. 3–5. The local supplemental extraction is `../../research-needs-and-proofs/Planidin-2025-supplement.txt`; the official associated implementation is available in [Zenodo record 16635603](https://zenodo.org/records/16635603).

Both experiments use secondary contact, with adults initially EEbb in deme 1 and eebb in deme 2. Migration is m = 1/4, divergent additive selection is s = 1/2, and recombination is r = 1/2. The genetic model has μ = 0. The pure-induction model has μ = 1/2 and φ = 1, so after epimutation the selected state is E in deme 1 and e in deme 2. During the first migration only, migrants from deme 1 into deme 2 are marked BB. Ordinary migration continues afterward, without further marking.

The deterministic life cycle is migration, viability selection with normalization by the receiving deme's mean fitness, recombination and gamete formation, random mating, and epimutation. Genotypes have fitness 1, 3/4, or 1/2 according to their number of locally maladapted selected alleles. The neutral marker itself does not affect fitness. With a common asymptotic marker frequency B-hat, the source barrier measure here is

```math
\operatorname{RI}=1-\frac{\widehat B}{m/2}=1-8\widehat B.
```

The finite comparison uses deterministic preselection migration pools followed by independent final offspring sampling, one diploid per deme. It is an explicit finite extension. In particular, replacing deterministic selection by the expectation of the finite transition kernel would be a different calculation: normalization by random mean fitness generally does not commute with expectation. The script here directly updates deterministic frequencies.

## Direct calculation and indexing

The independent script [deterministic_comparison.py](deterministic_comparison.py) tracks the ten unordered diploid genotypes in each deme. A haplotype is encoded as 2E + B, so the four values represent eb, eB, Eb, EB. At r = 1/2 the two parental and two recombinant haplotypes each receive one quarter of an adult's normalized reproductive contribution. Random mating forms the next adult frequencies by products of gamete frequencies. Pure induction changes only the selected bit, separately in each deme.

Generation 0 is the unmarked secondary-contact state. Generation 1 is the end of the complete first life cycle, including the sole marker pulse. For the genetic model let p denote the E frequency in deme 1; symmetry gives E frequency 1 − p in deme 2. Let

```math
\theta=(q_{1,e},q_{1,E},q_{2,e},q_{2,E}),\qquad
q_{d,a}=\Pr(B\mid\text{selected allele }a,\text{ deme }d).
```

The exact postpulse state is

```math
p_1=6/7,\qquad \theta_1=(0,0,0,1).
```

The two deme marker frequencies at a later generation are

```math
B_1=(1-p)\theta_1+p\theta_2,\qquad
B_2=p\theta_3+(1-p)\theta_4.
```

Subscripts on the right here label the four components; generation is suppressed. At finite times the script reports 1 − 8(B₁ + B₂)/2. The convergence proof below makes its limit the same as the source's common-deme definition.

## Why the conditional marker update is a convex combination

For the genetic model, each completed generation is in Hardy–Weinberg form for its four haplotypes, because the last substantive step is random mating. Whole-adult migration mixes two such populations; the receiving mixture need not itself be in Hardy–Weinberg form. The derivation keeps the source deme of each adult, so it does not assume Hardy–Weinberg proportions after migration.

Write Pℓ(a) for the selected-allele marginal in source deme ℓ; λdℓ is 3/4 for a local adult and 1/4 for a migrant. Let wd(a,c) be viability in destination deme d, Wd its mean fitness, and P′d(b) the selected-allele marginal in its next gametes. At free recombination one can choose the homologue supplying the selected allele and the homologue supplying the marker independently and uniformly. The same-homologue and different-homologue contributions give

```math
q'_{d,b}=\sum_{\ell,a} A_{(d,b),(\ell,a)}q_{\ell,a},
```
```math
A_{(d,b),(\ell,a)}=
\frac{\lambda_{d\ell}}{2W_dP'_d(b)}
\left[
\mathbf1_{a=b}P_\ell(a)\sum_cP_\ell(c)w_d(a,c)
+P_\ell(a)P_\ell(b)w_d(a,b)
\right].
```

These coefficients are nonnegative and each row sums to one: summing over the possible source marker backgrounds leaves exactly the probability of the destination selected allele b. The denominator is positive in the invariant region established below. Random mating preserves the gamete marker marginals, and μ = 0 changes nothing afterward. Thus this is the conditional update of the source recursion itself, rather than an assumed mixing property.

For reproducibility, the four rows can be written without probabilities. Before row normalization they are

```math
u=[3(1-p)(4-p),\;9p(1-p),\;p(3+p),\;3p(1-p)],
```
```math
v=[9p(1-p),\;3p(3+5p),\;3p(1-p),\;(1-p)(8-5p)].
```

The rows in order are u, v, reverse(v), reverse(u), normalized respectively by 12 − 8p², 8 + 8p + 8p², 8 + 8p + 8p², and 12 − 8p². These formulas follow by substituting the stated migration and viability values into A. The script checks, with exact rational arithmetic, that this reduced update and the full twenty-frequency recursion agree at generations 1, 2, 3, and 4. The algebraic derivation above supplies the all-generation reason; the finite comparison checks indexing and the computed prefix.

In particular, the smallest conditional marker frequency cannot decrease and the largest cannot increase under every subsequent genetic update.

## A common deterministic limit exists

Marginalizing the source recursion over the neutral marker gives

```math
p'=\frac{2+2p+2p^2}{5+2p},\qquad
p'-\frac23=\left(p-\frac23\right)\frac{2(p+1)}{5+2p}.
```

One way to verify the first formula is to use the preselection mean selected frequency z = 1/4 + p/2 and the mean squared source frequency v = p² − p/2 + 1/4. The E-gamete numerator is (3/4)z + (1/4)v, and mean fitness is 1/2 + z/2. This uses the migrated mixture of source Hardy–Weinberg populations, not a Hardy–Weinberg replacement for that mixture.

Starting at p₁ = 6/7, the interval [2/3, 6/7] is invariant. The displayed multiplier is positive and less than one there, so p decreases to 2/3. Every selected background in both demes consequently has probability at least 1/7 at all generations under discussion.

The different-homologue contribution in A alone now gives a uniform bound for every one of its sixteen entries:

```math
A_{ij}\ge
\frac{\lambda_{d\ell}P_\ell(a)P_\ell(b)w_d(a,b)}{2W_dP'_d(b)}
\ge \frac{(1/4)(1/7)^2(1/2)}2=\frac1{784}.
```

Here Wd and P′d(b) are at most one. Removing 1/784 from each of the four entries of each row and renormalizing shows that the conditional range contracts by at most

```math
\max\theta'-\min\theta'\le\frac{195}{196}(\max\theta-\min\theta).
```

The minimum and maximum are bounded monotone sequences. Their difference tends to zero, so all four conditional marker frequencies converge to the same c. Both deme marker frequencies, being convex combinations of them, also converge to c. This proves existence of the genetic B-hat and RI limit. The contraction estimate is deliberately coarse; no floating-point residual is being used as a mathematical error bound.

## Exact strict genetic bound from four generations

Exact rational iteration gives, in the order defined above,

```math
\theta_4=\left(
\frac{158042799831}{2612298864200},
\frac{825778109695}{18042773705392},
\frac{1228259142369}{18042773705392},
\frac{172444392929}{2612298864200}
\right).
```

The largest component is

```math
M=\frac{1228259142369}{18042773705392}<\frac1{14}.
```

The convex-combination invariant implies c ≤ M, and hence the following exact strict comparison, independently of any reported numerical digits:

```math
\operatorname{RI}_{\rm genetic}
\ge1-8M
=\frac{1027087570805}{2255346713174}
>\frac37,
```
```math
(1-8M)-\frac37=\frac{423572856113}{15787426992218}>0.
```

The prefix is checked by Python's exact `Fraction` arithmetic; the compatibility, invariance, and convergence arguments are written mathematics here. This note does not call that combination Lean checked.

## Pure induction is exactly solvable

At the end of each pure-induction generation all selected alleles are locally adapted. During the marked first migration, incoming adults in deme 2 have weighted mass m(1 − s) = 1/8, while local adults have mass 1 − m = 3/4. Thus the postpulse marker means are (B₁, B₂) = (0, 1/7).

For every later generation the local and immigrant viable contributions are in the ratio 6:1. Recombination, random mating, and selected-state resetting do not alter the neutral marker mean. Consequently

```math
\binom{B'_1}{B'_2}
=\begin{pmatrix}6/7&1/7\\1/7&6/7\end{pmatrix}
\binom{B_1}{B_2}.
```

The mean stays 1/14 and the deme difference contracts by 5/7. Therefore B-hat = 1/14 and RIepigenetic = 3/7 exactly. Combining this with the previous strict genetic bound proves the deterministic ranking.

## Numerical precision and interpretation

The script was run at 50 decimal digits for 500 generations and at 90 digits for 1000 generations. It checks nonnegativity and normalization at every generation. The 90-digit genetic RI values include:

| Generation | Genetic RI, shortened |
|---:|---:|
| 4 | 0.52928321029185602439 |
| 10 | 0.53156830411595921024 |
| 20 | 0.53156909302730731072 |
| 50 | 0.53156909302856497295 |
| 1000 | 0.53156909302856497295 |

The final long value was 0.531569093028564972945935888885575265492561384576022213437273810235122548596769981211214948. Agreement across precisions and horizons supports the reported approximation but does not certify all those digits. The written argument proves limit existence and the strict ranking; it does not yet turn the displayed high-precision approximation into a validated decimal enclosure.

This single matched case establishes a ranking reversal for this particular finite extension at N = 1, m = 1/4, s = r = 1/2, under the specified initial condition and pulse. It does not establish a general monotone effect of population size, a reversal for other finite life cycles, empirical reproductive isolation, or novelty relative to all previous work. It supplies a sharper, falsifiable comparison than a general statement that finite populations strengthen epigenetic barriers.

To reproduce, run `python deterministic_comparison.py` from a Python installation; only the standard library is used. The script reads the two existing finite-result JSON files to display the comparison and does not modify them. It prints the numerical diagnostics, exact prefix certificate, and exact full/reduced recurrence comparison.

## Verification addendum, 2026-09-25

Historical draft/audit statements above are preserved. The [combined receipt](verification/combined-receipt.json) records 34 selected endpoints across FiniteFixation, FiniteEpigenetic, DeterministicEpigenetic and RankingReversal. The final deterministic source hash is ece655b0af42fbd580ca86b3f8176a8b4323fe3fd716da9429f13f6366f3117f. Changes after its reviewed draft repaired proof syntax/status text without changing the recurrence or mathematical statements. Reports use only propext, Classical.choice and Quot.sound. RankingReversal imported the preserved deterministic object and exited zero; the earlier deterministic process exit remains unretrieved and explicitly null. This addendum does not extend formal scope to source transport or deterministic common-limit existence.
