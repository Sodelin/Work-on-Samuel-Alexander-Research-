# A conditional positive example

The exact population law of rooted gene-tree topologies identifies a rooted species-tree topology in this prescribed three-taxon model. This is an elementary formalization of a known result, with no claim of new biology.

The primary source is Allman, Degnan, and Rhodes, *Identifying the Rooted Species Tree from the Distribution of Unrooted Gene Trees under the Coalescent*, [arXiv:0912.4472v2, Introduction, example surrounding Eq. (1)](https://arxiv.org/html/0912.4472v2#S1). For a designated rooted topology $`s`$ on three labeled taxa and internal branch length $`t`$ in coalescent units, it states

```math
P(g=s)=1-\frac{2}{3}e^{-t},\qquad P(g\ne s)=\frac{1}{3}e^{-t}.
```

Put $`c=e^{-t}`$. For $`t>0`$, $`0<c<1`$, so the matching probability exceeds either alternative by $`1-c>0`$. The paper also states the general rooted-triple identifiability result in Proposition 1.

## What the Lean file checks

`ThreeTaxonIdentifiability.lean` defines three topology labels and the displayed polynomial law. It proves:

- Nonnegative probabilities when $`0\le c\le1`$, summing to one.
- The gap between the designated topology and each alternative is exactly $`1-c`$.
- For $`c<1`$, the designated topology is the unique probability maximizer.
- For $`c,d<1`$, equality of laws implies equality of both topology and transformed parameter, including when the parameters initially differ.
- For $`c=1`$, all probabilities are $`1/3`$, all designated labels give the same law, and no decoder recovers every resolved label from that law.

The nonnegativity condition is needed to interpret the formula as a probability law. The algebraic uniqueness proofs themselves only require the strict upper bound.

## Scope

The **data object** in the theorem is an exact probability function on rooted gene-tree topologies. It is not a finite list of loci or raw genomic sequences. The **model input** is the prescribed formula. The **target** is a rooted relationship among three already designated, labeled taxa. The theorem does not delimit species, establish reproductive compatibility, identify an unrestricted biological species concept, or promise certainty from finite samples.

The derivation of the multispecies coalescent formula and the exponential substitution are not formalized here. The $`c=1`$ theorem records the collapse of the resolved topology parameter at a zero internal branch; it does not claim three different positive-length species trees have the same law. The Lean result is a conditional statement whose biological applicability depends on the model and observation assumptions.

## Reproduce

From a prepared repository checkout, enter `real` and run `lake env lean ../research/open-questions/genomic-identifiability/positive/ThreeTaxonIdentifiability.lean`. This uses the repository-pinned Lean 4.33.1 and Mathlib environment. The archived local run used the installed compiler directly with the same existing cache, without downloads or checkout edits. A successful run exits with code zero and prints the foundational axioms used by the main theorems; `sorryAx` should be absent.
