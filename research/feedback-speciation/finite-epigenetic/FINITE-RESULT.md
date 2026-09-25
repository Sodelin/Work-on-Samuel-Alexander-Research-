# Exact finite-population comparison of genetic and epigenetic barriers

Status: the finite comparison below is checked in Lean 4.33.1. The deterministic ordering from generation four onward and the joint ranking reversal are also checked; see the [combined receipt](verification/combined-receipt.json). Deterministic common-limit existence remains a written proof outside these modules. This document is a research note and reproducible example; novelty and journal or VibeMathed eligibility are not established.

## The result

Consider the explicitly defined offspring-sampling model below, with one diploid adult in each of two demes. Both models start from the same secondary-contact background. Their only difference is whether the selected locus is genetically inherited without mutation or is reset to the locally favored epigenetic state after reproduction.

The limiting probability that a one-off neutral immigrant marker fixes globally is

```math
p_{\mathrm{gen}}=\frac{323808055}{4466354606},
\qquad p_{\mathrm{epi}}=\frac1{14}.
```

Normalize by the introduced preselection marker dose $`B_0=m/2=1/8`$, and define the fixation-based barrier measure $`RI=1-p/B_0`$. Then

```math
RI_{\mathrm{gen}}=\frac{937945083}{2233177303},
\qquad RI_{\mathrm{epi}}=\frac37,
\qquad
RI_{\mathrm{epi}}-RI_{\mathrm{gen}}
=\frac{19130904}{2233177303}>0.
```

These are exact fractions. The calculation uses a finite Markov kernel, not Monte Carlo sampling. The Lean proof connects the harmonic certificate to actual finite-time marginal probabilities and gives, for both models,

```math
\left|\Pr(\text{all four marker copies are B after }n\text{ post-pulse steps})-p\right|
\le (99/100)^n.
```

The marker-fixed and marker-lost classes can each contain many states: selected alleles may continue to change inside them.

## Source and precise finite extension

The source is Planidin et al. (2025), [Adaptive epigenetic divergence can facilitate ecological speciation](https://pmc.ncbi.nlm.nih.gov/articles/PMC12440623/), especially the model, the neutral-marker measure, the [supplement](https://ndownloader.figshare.com/files/57066856), and the finite-population direction in its conclusion.

The source uses deterministic recursions. We add independent finite offspring sampling after the source life cycle. This is a declared mathematical extension, not the authors' program or a claim that there is a unique finite counterpart. [SOURCE-MODEL-CONTRACT.md](SOURCE-MODEL-CONTRACT.md) records stage order and source details.

- Migration rate is $`m=1/4`$ in both directions.
- Selection is additive on the selected E/e locus with $`s=1/2`$. Deme 1 favors E, and deme 2 favors e.
- Recombination is $`r=1/2`$. Both demes have one diploid adult.
- Migration creates weighted adult pools. Destination-specific viability selection is normalized within the pool. Two independent gametes then form each offspring. Offspring in the two demes are sampled independently.
- In the genetic comparison, $`\mu=0`$. In the pure-induction comparison, $`\mu=1/2,\phi=1`$: the selected copies are reset after mating to EE in deme 1 and ee in deme 2.
- Selfing is permitted by independent gamete sampling. There is no separate integer-migrant census before viability selection.
- The shared starting adults are EEbb in deme 1 and eebb in deme 2. A single pulse labels the deme-1-to-deme-2 migrant contribution BB before its destination selection. Later migration introduces no new marker copies.

The preselection marker dose and the postselection marker frequency differ; replacing the former denominator with the latter would change the measure.

## How the proof works

The reference computation keeps all ten phased diploid genotypes, giving 100 two-deme states. At free recombination, phase can be discarded: each adult is determined for future dynamics by its E-copy and B-copy counts. This gives 81 states.

The source correspondence and this reduction were independently checked with exact rational arithmetic against every row of both 100-state kernels. The Lean model starts from the explicit 81-state count formulas. The reduction from the phased model is an independently audited mathematical and computational correspondence; it is not an additional Lean theorem.

Every count-model transition is a nonnegative integer numerator divided by a positive row denominator. The candidate fixation vector is also rational, with common denominator 3,720,412 for the genetic model and 8,580 for the epigenetic model. Lean's kernel checks all integer identities:

1. Every transition row sums to its denominator.
2. Boundary classes are closed and the certificate is respectively zero or one on them.
3. The certificate lies in [0,1] and is harmonic for every row.
4. Each row has terminal probability at least 1/100.
5. The pulse is a probability distribution and its certificate average has the stated exact value.

A generic finite-distribution theorem then proves the geometric error bound and epsilon convergence. No unproved absorption assumption, custom axiom, placeholder proof, or native-computation oracle is used. The actual minimum terminal probability found by the independent exact check is 72/2401; the proof deliberately uses the simpler valid bound 1/100.

## What this does and does not answer

This resolves one exact finite-population comparison with a matched initialization. It gives a tractable test case for the authors' finite-population research direction.

The pure-induction scalar formula is already present in the source supplement; it is a benchmark, not claimed as a new discovery. Fixation-based barrier measures also have prior literature. [PRIOR-WORK.md](PRIOR-WORK.md) identifies these nearest results. The potentially useful additional contribution is the fully specified finite comparison and its relationship to the deterministic comparison.

This is not a universal monotonicity theorem in population size, a theorem that DNA uniquely identifies species, or a proof that reduced marker transmission creates a new biological species. Cultural transmission and epigenetic modifiers are not in this model. The work is distinct from completion of Wong et al. (2024), whose stochastic ARG and representation obligations remain separately recorded.

## Reproduction and evidence

- [FiniteFixation.lean](FiniteFixation.lean): forward marginal recursion, harmonic certificates, finite-time error and pulse-mixture convergence.
- [FiniteEpigenetic.lean](FiniteEpigenetic.lean): concrete count kernel, integer checks, exact pulse values and strict comparison.
- [finite_life_cycle.py](finite_life_cycle.py): full phased reference model.
- [count_model.py](count_model.py): count specialization and exact checks against both phased kernels.
- [count-certificates.json](count-certificates.json): generated integer certificate data.
- [INDEPENDENT-MODEL-AUDIT.md](INDEPENDENT-MODEL-AUDIT.md): independent regeneration and source-fidelity audit.
- [verification/finite-receipt.json](verification/finite-receipt.json): source hashes, compiler logs, and 21 selected checked endpoints.

From this directory, using Lean 4.33.1 and the pinned Mathlib dependencies recorded in the receipt:

~~~powershell
& .\Check.ps1 -File FiniteFixation.lean
& .\Check.ps1 -File FiniteEpigenetic.lean
~~~

Run the two commands sequentially. The runner emits local oleans into build/ and compiler logs into verification/. The Python commands use only the standard library:

~~~powershell
python finite_life_cycle.py --m 1/4 --s 1/2 --r 1/2 --mu 0 --exact --output genetic-exact.json
python finite_life_cycle.py --m 1/4 --s 1/2 --r 1/2 --mu 1/2 --exact --output epigenetic-exact.json
python count_model.py
~~~

Use ordinary Python execution, without -O; count_model.py uses assertions for its exact correspondence checks. The seconds fields in the reference result JSON are runtime metadata, so freshly generated files can have different hashes while mathematical data agree.
