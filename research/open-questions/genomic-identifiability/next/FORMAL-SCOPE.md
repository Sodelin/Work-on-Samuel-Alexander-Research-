# Finite evidence and three-taxon identifiability

This isolated extension makes the previous exact-law result useful for finite observations: it distinguishes positive evidence from certainty and proves an exact error margin for recovering a rooted relationship. It is a formalization of elementary consequences of a known model; no mathematical or biological novelty is claimed.

## Checked result

There are three rooted topologies on already designated taxa. The prescribed law is

```math
P_{s,c}(g)=\begin{cases}1-2c/3 & g=s,\\c/3 & g\ne s.\end{cases}
```

The three-taxon coalescent interpretation is $`c=e^{-t}`$, where $`t`$ is the internal branch length. The classical formula and wider identifiability context appear in [Allman, Degnan and Rhodes (2011), Introduction, Proposition 1 and the example around Equation (1)](https://jarhodesuaf.github.io/papers/STfromUnrootedGTs.pdf). This extension prescribes that formula and does not derive the stochastic process or exponential substitution.

[ThreeTaxonFiniteEvidence.lean](ThreeTaxonFiniteEvidence.lean) proves:

1. **Finite samples have overlapping support.** If $`0<c\le 1`$, every specified finite ordered sample has strictly positive product mass under every topology label. This remains true when two labels use different positive parameters. Thus a finite sample cannot rule out any label by zero probability in this model.
2. **No finite decoder is uniformly certain.** For every finite sample size and every deterministic decoder, there is a label and possible sample on which the decoder is wrong. A quantitative witness has singleton mass at least $`(c/3)^n`$. This is an existential adverse label for each decoder, not an assertion that every decoder errs under every label. The module checks singleton masses; it does not formalize a probability measure or aggregate error probability.
3. **A positive robust recovery theorem.** Let $`q`$ estimate the three probabilities. If $`|q(g)-P(g)|\le\varepsilon`$ for every topology and $`2\varepsilon<1-c`$, the true label remains the strict maximizer of $`q`$. Consequently every maximizer chosen from $`q`$ is correct. This deterministic statement can be applied to empirical frequencies once a separate statistical argument justifies their error bound.
4. **The strict margin is sharp.** At error $`(1-c)/2`$, the valid probability vector $`(1/2-c/6,\,1/2-c/6,\,c/3)`$ can tie the true label with an alternative. A non-strict error threshold alone cannot ensure unique-mode recovery.

For example, $`c=1/2`$ yields true probabilities $`(2/3,\,1/6,\,1/6)`$ and gap $`1/2`$. Accuracy strictly better than $`1/4`$ preserves the true mode. At accuracy exactly $`1/4`$, $`(5/12,\,5/12,\,1/6)`$ ties two labels. At the same time, a finite string consisting entirely of an alternative has positive probability $`(1/6)^n`$. Exact-law identification, finite-sample uncertainty and robust estimation therefore coexist.

The sample product is explicitly an independent-locus model. The robust margin theorem itself is deterministic and needs no independence premise. The boundary $`c=0`$ is excluded from the support theorem: the law is then concentrated at its designated label. At $`c=1`$ the three laws coincide and the positive margin vanishes.

## Biological and Alexander scope

The target is a rooted relationship among three preassigned taxa. No label is defined to mean a discovered biological species, and no theorem identifies species boundaries, reproductive compatibility or Alexander's specieslike subsets. The required empirical bridge includes defensible taxon assignment, appropriately reconstructed rooted gene trees, model adequacy and a justified treatment of dependence between loci. Genomic sequence reconstruction error must be accounted for before applying the probability margin.

The three-taxon restriction matters. A general rule that selects the most probable complete gene-tree topology can fail for larger trees under the same coalescent framework; see [Degnan and Rosenberg (2006)](https://journals.plos.org/plosgenetics/article?id=10.1371/journal.pgen.0020068). This module claims no such general rule.

For Alexander research, the contribution is methodological: it shows how to state a species-related inference target, prove limitations of finite evidence, and state a quantitative condition for positive inference. Applying this pattern to the project's infinite-population specieslike predicate still requires an observation model and admissible-continuation assumptions that constrain that predicate. The present module does not supply those assumptions or overcome the finite-gARG completion obstruction.

## A separate statistical extension, not machine checked here

For $`n>0`$ independent, exactly observed gene-tree topologies from this law, let the estimate select a most frequent topology. Put $`\Delta=1-c>0`$. For each of the two alternatives $`a`$, define $`Y_i=\mathbf{1}_{\{G_i=s\}}-\mathbf{1}_{\{G_i=a\}}`$. Its range is $`[-1,1]`$ and mean is $`\Delta`$. The usual bounded-variable inequality gives $`\Pr(\overline Y\le0)\le e^{-n\Delta^2/2}`$. Taking a union over the two alternatives yields

```math
\Pr(\widehat s\ne s)\le\min\{1,\;2\exp[-n(1-c)^2/2]\}.
```

This displayed bound is a paper derivation using [Hoeffding (1963), Probability Inequalities for Sums of Bounded Random Variables](https://doi.org/10.1080/01621459.1963.10500830), not an endpoint verified in the accompanying Lean module. It includes adverse tie breaking. It would imply confidence $`1-\delta`$ when $`n\ge 2\log(2/\delta)/(1-c)^2`$ under those assumptions. This is a standard application, not a new statistical theorem. Directly validating these probabilistic premises is the useful next empirical step; real loci must not be treated as independent by default.

## Verification and reproduction

Local Lean 4.33.1 verification completed with exit code zero. Eight selected endpoints use only `propext`, `Classical.choice` and `Quot.sound`. The final compiler run had no warnings or errors. The receipt records the source hash and exact endpoint inventory in [verification.json](verification.json); [validation.txt](validation.txt) records its endpoint output.

Run `Check.ps1` from this folder. It invokes the already installed Lean compiler and existing Mathlib cache, writes no owner repository files, and downloads nothing. The Mathlib revision declared by the owner environment is `0df444a360eaa60ab8c11dca51a86af692955474`. This local result has not been integrated into the owner repository's build or its aggregate endpoint counts.

## Publication integration

This module is selected by the repository standalone research-artifact auditor after the fresh core and real library builds. The exact-commit hosted result is recorded in [PR #6 checks](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/pull/6/checks). The original local receipt above records its pre-integration environment.
