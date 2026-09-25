# Initial audit: Big ARG rates, expected event counts and normalization

**Status: bounded primary-source and written mathematical audit. No Lean probability theorem, correction submission or novelty claim has been made.**

## Finding

For a lineage-count process started with two lineages, absorbed on first reaching one, and with literal rates

```math
\lambda_k=k\rho,\qquad \mu_k=\binom{k}{2},\qquad k\geq2,
```

the written calculation gives

```math
\mathbb E_2[B]=e^{2\rho}-1,\qquad
\mathbb E_2[J]=2e^{2\rho}-1.
```

Here $`B`$ counts upward/recombination events and $`J`$ counts all merger and recombination events **after the initial sampling nodes**. Counting those two initial sampling nodes adds two to the second expression.

Thus the conjectured factor of two in the exponent is real for this stated chain. There is also an independently verified conventional parameterization with $`\lambda_k=k\theta/2`$, $`\mu_k=\binom{k}{2}`$; in that parameter, the same expressions are $`e^\theta-1`$ and $`2e^\theta-1`$. The two descriptions agree when $`\theta=2\rho`$.

A strict expected-event asymptotic $`O(e^\rho)`$ as $`\rho\to\infty`$ cannot be certified from the first displayed rate pair. The source's qualitative conclusion that the Big ARG becomes exponentially costly remains compatible with either convention. We should record a **normalization/interpretation issue requiring clarification**, without presenting it as a newly discovered theorem or announcing an author error.

## 1. Primary-source observations

### 1.1 Wong et al. (2024), Appendix B

[Published article](https://pmc.ncbi.nlm.nih.gov/articles/PMC11373519/); [version-of-record PDF](https://www.pure.ed.ac.uk/ws/portalfiles/portal/458588307/iyae100.pdf); [DOI](https://doi.org/10.1093/genetics/iyae100).

The local full-text XML's section `app2` is **The big and little ARG** (printed journal p. 13, zero-based PDF page 13 because of its cover sheet). The relevant MathML identifiers are:

| Identifier | Exact mathematical content / context |
|---|---|
| `IM29` | Little ARG recombination intensity $`\rho\nu/(m-1)`$. |
| `IM30` | $`\rho\geq0`$, described as a per-genome recombination rate. |
| `IM31` | Little ARG common-ancestor intensity $`\binom{\|L\|}{2}`$. |
| `IM38` | Big ARG common-ancestor intensity $`\binom{\|L\|}{2}`$. |
| `IM39` | Big ARG recombination intensity $`\|L\|\rho`$. |
| Following `IM40` | Big ARG stopping rule: only one lineage remains. |
| `IM41` | Big ARG event-number comparison $`O(e^\rho)`$, citing Griffiths and Marjoram (1997). |
| `IM42` | Little ARG comparison $`O(\rho^2)`$; this audit does not establish it. |

The Big-O sentence does **not** explicitly specify expectation, a probability mode, fixed sample size, or the parameter limit. Treating it as expected event count at fixed sample size is a mathematical interpretation to make explicit, not wording already supplied by the source.

The XML is decisive about the binomial coefficient: plain PDF text extraction flattens it into a misleading `|L|2` string.

### 1.2 Independently verified convention and expectation formula

Bob Griffiths, **2nd Cornell Probability Summer School (2006)**, author-origin lecture material hosted by Duke University: [PDF](https://sites.math.duke.edu/~rtd/CPSS2006/griffiths.pdf).

- PDF page 34 (zero-based index 33), **Ancestral Recombination Graph**, gives merger intensity $`k(k-1)/2`$, split intensity $`k\theta/2`$, with the source naming its parameter $`\rho=2Nr`$. We rename that parameter $`\theta`$ here to avoid identifying distinct conventions.
- PDF page 35 (index 34) gives upward/downward jump probabilities $`\theta/(\theta+k-1)`$ and $`(k-1)/(\theta+k-1)`$, with absorption at one.
- The same page states a formula for recombination events through the grand first common ancestor:

```math
\mathbb E[R_n^1]
=\theta\int_0^1
\frac{1-(1-x)^{n-1}}{x}\,e^{\theta x}\,dx.
```

The integrand's apparent singularity at zero has a continuous polynomial extension for integer $`n\geq2`$. At $`n=2`$ the factor before the exponential is one, so the formula evaluates to $`e^\theta-1`$.

The lecture also gives the expected time to the grand MRCA. At $`n=2`$ it yields $`2(e^\theta-1-\theta)/\theta^2`$, agreeing with the occupation calculation below.

### 1.3 What remains unread or unverified

The cited 1997 chapter is Griffiths and Marjoram, **An ancestral recombination graph**, pp. 257–270 in *Progress in Population Genetics and Human Evolution*, DOI [10.1007/978-1-4757-2609-1_16](https://doi.org/10.1007/978-1-4757-2609-1_16). Its identity was corroborated by the authors' [Monash publication record](https://research.monash.edu/en/publications/an-ancestral-recombination-graph/).

Direct Springer chapter and PDF requests failed during this pass. The original chapter's precise parameter definition, theorem wording and asymptotic qualification were **not read**. The 2006 lecture confirms the author-associated convention and exact expectation independently; it is not evidence that the 1997 chapter uses identical notation in every respect.

Visual screenshot requests for the available PDFs timed out. The lecture statements above were read from the browser's extracted full PDF text; Wong's formulas were additionally checked against the local structured MathML. No claim depends on treating a failed screenshot as evidence.

## 2. Convention-independent mathematical contract

Fix constants $`a>0`$ and $`b\geq0`$. Let $`K`$ be the time-homogeneous birth-death chain on positive integers, stopped at one, with rates for $`k\geq2`$

```math
\lambda_k=bk,\qquad
\mu_k=\frac{a k(k-1)}2.
```

Define the dimensionless ratio

```math
\theta=\frac{2b}{a}.
```

The embedded chain has probabilities

```math
p_k=\frac{\theta}{\theta+k-1},\qquad
q_k=\frac{k-1}{\theta+k-1}.
```

This formulation separates uniform changes in the clock from changes in the branching-to-merging ratio. Multiplying both rates by the same positive constant changes holding times but leaves event counts unchanged. Multiplying only the birth rate changes $`\theta`$ and therefore changes their exponential growth.

### 2.1 Almost-sure absorption, without assuming finite expected cost

For $`b=0`$, the chain moves down deterministically and absorption is immediate after $`n-1`$ jumps.

For $`\theta>0`$, consider the embedded chain killed at either 1 or an integer $`M>2`$. The elementary gambler's-ruin difference equation gives

```math
\mathbb P_2(\tau_M<\tau_1)
=\left(\sum_{j=1}^{M-1}\frac{(j-1)!}{\theta^{j-1}}\right)^{-1}.
```

Indeed, successive differences of a harmonic hitting-probability function satisfy $`d_{k+1}=(q_k/p_k)d_k=((k-1)/\theta)d_k`$; imposing endpoint values zero and one gives the expression.

The denominator diverges as $`M\to\infty`$: eventually consecutive terms have ratio greater than two. Thus the probability of reaching arbitrarily large states before one is zero.

A path remaining forever in a fixed finite set $`\{2,\ldots,M-1\}`$ while avoiding one also has probability zero. From each such state there is a uniformly positive probability of taking enough successive downward steps to hit one within $`M`$ jumps. Applying the Markov property in blocks yields a geometric bound on continued avoidance.

Every nonabsorbed path is either bounded or unbounded, so absorption occurs after finitely many jumps almost surely. Conditional on those finitely many visited states, the holding times have finite rates and are almost surely finite. This constructs a nonexplosive chain up to the stated stopping time without assuming the desired expectation formula.

For fixed initial $`n>2`$, the same finite-barrier argument applies. It also follows by the finite-state numerator version of the displayed ruin formula.

### 2.2 Occupation calculation for initial state two

Let $`T_k`$ denote the **expected total time** spent at state $`k`$ before absorption. A path starting at two crosses $`2\to1`$ exactly once. Counting downcrossings by expected visits, or using the jump-intensity compensation identity, gives

```math
\mu_2T_2=1,\qquad T_2=\frac1a.
```

For each $`k\geq2`$, the number of upcrossings $`k\to k+1`$ equals the number of downcrossings $`k+1\to k`$ on every absorbed path. Hence

```math
\lambda_kT_k=\mu_{k+1}T_{k+1},
\qquad
T_{k+1}=\frac{\theta}{k+1}T_k.
```

Induction yields

```math
T_k=\frac{2\theta^{k-2}}{a k!},\qquad k\geq2.
```

There is no integrability circle here. The first downcrossing identity gives finite expected visits at two, and each successive crossing identity propagates finiteness to the next state. Nonnegative counts permit Tonelli even before the infinite sum is known finite.

Summing expected birth events over states gives

```math
\mathbb E_2[B]
=\sum_{k=2}^{\infty}\lambda_kT_k
=\sum_{k=2}^{\infty}\frac{\theta^{k-1}}{(k-1)!}
=e^\theta-1.
```

If $`C`$ counts mergers, the pathwise conservation identity is $`2+B-C=1`$. Therefore

```math
C=B+1,\qquad J=B+C=2B+1,
```

and

```math
\mathbb E_2[C]=e^\theta,\qquad
\mathbb E_2[J]=2e^\theta-1.
```

These formulas remain valid at $`\theta=0`$. Summing the occupations also gives, for $`\theta>0`$,

```math
\mathbb E_2[\tau_1]
=\frac{2(e^\theta-1-\theta)}{a\theta^2},
```

with continuous limit $`1/a`$ at zero.

### 2.3 Fixed initial sample size $`n\geq2`$

The cut-crossing balance becomes

```math
\mu_kT_k-\lambda_{k-1}T_{k-1}
=\mathbf1_{\{2\leq k\leq n\}},
```

where the incoming occupation term is zero at $`k=2`$. Solving the recurrence gives

```math
T_k=\frac{2}{a k!}
\sum_{j=2}^{\min(k,n)}(j-2)!\,\theta^{k-j}.
```

Summing births and expanding the exponential yields the equivalent integral

```math
B_n:=\mathbb E_n[B]
=\theta\int_0^1
\left(\sum_{j=0}^{n-2}(1-x)^j\right)e^{\theta x}\,dx.
```

For $`\theta>0`$, another exact expression is

```math
B_n=\sum_{j=2}^{n}(j-2)!\,\theta^{2-j}
\left(e^\theta-\sum_{r=0}^{j-2}\frac{\theta^r}{r!}\right).
```

The sum-of-nonnegative-series version is preferable for a first formal proof because it handles $`\theta=0`$ without removable singularities. Pathwise,

```math
J=2B+n-1.
```

Since the polynomial in the integral lies between 1 and $`n-1`$ on $`[0,1]`$,

```math
e^\theta-1\leq B_n\leq(n-1)(e^\theta-1).
```

Thus, for **fixed** $`n\geq2`$ as $`\theta\to\infty`$, expected recombinations and total post-sampling events are $`\Theta(e^\theta)`$. This statement is not uniform in an independently growing sample size. The cited lecture separately discusses $`n\to\infty`$ with its recombination parameter fixed; the regimes must not be conflated.

## 3. Consequences for the Wong rate reading

| Rate convention | Dimensionless parameter | $`\mathbb E_2[B]`$ | $`\mathbb E_2[J]`$ |
|---|---|---|---|
| Wong Appendix B displayed rates: $`a=1,b=\rho`$ | $`\theta=2\rho`$ | $`e^{2\rho}-1`$ | $`2e^{2\rho}-1`$ |
| Griffiths lecture: $`a=1,b=\theta/2`$ | $`\theta`$ | $`e^\theta-1`$ | $`2e^\theta-1`$ |
| Uniform clock rescaling of either row | Unchanged ratio $`2b/a`$ | Unchanged | Unchanged |

In the literal first row,

```math
\frac{\mathbb E_2[J]}{e^\rho}
=2e^\rho-e^{-\rho}\longrightarrow\infty.
```

So `expected total events = O(exp rho)` in the strict fixed-$`n`$, $`\rho\to\infty`$ sense would be false under that rate convention. Writing $`\exp(\Theta(\rho))`$ captures the qualitative exponential comparison while leaving the convention explicit. We must not silently replace the source's $`\rho`$ by a doubled variable in a theorem advertised as a literal formalization.

The source's Big-O is attached to an event-number/runtime comparison and does not define a probabilistic complexity notion. Consequently this audit establishes an exact chain result and a mismatch under one natural interpretation; it does not establish the authors' intended meaning or a formal erratum.

Counting initial sample nodes, distinguishing births from all jumps, or globally rescaling time changes additive or multiplicative constants outside the exponential. Those choices do not remove the factor-of-two issue in the exponent when the same parameter symbol is held fixed.

## 4. Relation to spatially annotated Big ARGs

In the Big ARG described here, branch selection and breakpoint marks do not alter the count-level transition rates. Each split increases the lineage count by one, and each merger decreases it by one. Hence the count process is a projection of a properly constructed marked ARG process.

That projection still needs to be proved in a complete stochastic formalization. A birth-death theorem alone does not construct parent selection, breakpoint distributions, genomic interval labels or the finite graph output. Conversely, the detailed marks cannot change this event-count calculation if they leave the displayed aggregate rates and stopping rule unchanged.

The Little ARG removes or shortens lineages using ancestral material, so its count evolution is different. No conclusion about its $`O(\rho^2)`$ complexity, its coupling to the Big ARG or equality of its local genealogies has been proved by this calculation. Those are separate source obligations.

## 5. Exact proposed Lean proof contract

The following order prevents a convenient-model theorem being mislabeled as full source verification:

1. **Declare parameters separately:** `mergeScale a > 0`, `splitScale b >= 0`, and `theta = 2*b/a`. Prove the normalized jump-probability identities algebraically.
2. **Construct the absorbed stochastic chain** (or its embedded Markov chain plus holding times), with initial $`n\geq2`$, explicit absorption at one and the stated transition kernel.
3. **Prove almost-sure finite jump absorption** using finite-barrier hitting probabilities and bounded-state avoidance. An assumption that absorption is already certain would omit one of Appendix B's claims.
4. **Prove pathwise event conservation:** `mergers = recombinations + n - 1`; specify whether initial sampling nodes count as events.
5. **Derive occupation/crossing identities from that probability model.** If only a recurrence is formalized, label it a recurrence theorem; do not call its solution an expected event count without the semantic connection.
6. **Prove the occupation solution and summability** using nonnegative sums. Derive $`\mathbb E_2[B]=\exp(2b/a)-1`$ and $`\mathbb E_2[J]=2\exp(2b/a)-1`$; then extend to fixed finite $`n`$ if needed.
7. **State asymptotics with a named regime:** fixed $`n`$, positive fixed merger scale, branching ratio tending to infinity. Prove the $`\Theta`$ bounds rather than repeating an unspecified Big-O.
8. **Export both source-convention specializations:** Wong's displayed rates and the independently verified Griffiths normalization, with explicit substitution. Preserve the normalization issue in the claim ledger.
9. **For full Big ARG coverage**, separately construct the marked graph process and prove its lineage-count projection follows this chain. Only then transfer the expectation theorem to that process.

A deterministic rate recurrence with assumed crossing identities is a useful intermediate theorem, but it would leave Steps 2, 3, 5 and 9 open. It must not be counted as a complete stochastic formalization.

## 6. Bounded audit disposition

- **Established in the written audit:** the exact count-chain formula, convention mapping, fixed-sample-size exponential bounds, and why clock scaling / node-count conventions cannot absorb the parameter mismatch.
- **Primary corroboration:** Griffiths's own 2006 jump probabilities and integral expectation formula agree with the independent derivation.
- **Not verified:** full text of the 1997 chapter; the intended probabilistic meaning of Wong's Big-O; any published correction or author clarification; a Lean construction/proof of this stochastic process; spatial-marked process equivalence; Little ARG complexity.
- **Recommended public wording until resolved:** “The Appendix B rate normalization is being audited. Literal displayed rates give exponent $`2\rho`$ for expected event counts; the customary half-rate convention gives exponent $`\rho`$. The qualitative exponential comparison is consistent with both. No correction claim is being made.”

---

Local source XML SHA-256: `2b77c349f39d2885b3e36d3bcab639a7ef3b9c6217263031aa4bc8f1c2a0d05e`.

Audit completed UTC: `2026-09-25T13:02:02.503918+00:00`.
