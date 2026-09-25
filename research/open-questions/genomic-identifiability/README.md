# What can genomic evidence determine about species?

**New follow-up:** [What is already known about DNA-based identification, and the checked finite-evidence extension](next/README.md).

Date: 25 September 2026. This note responds to the proposed goal of proving that genomic data determines biological species. It distinguishes a general identification question, a newly checked consequence of the project's ancestry model, and an elementary formalization of a known positive example.

## The research question is important, but needs three definitions

A claim of exact recovery must specify **the observation**, **the class of admissible biological histories**, and **the quantity to be recovered**. Raw DNA sequences, a reconstructed ancestry graph, and an exact probability distribution are different observations. A species partition, reproductive compatibility, a species-tree topology, and Alexander's specieslike property are different targets.

This distinction has a biological literature: de Queiroz separates a species concept from the evidence used to delimit species, discussing reproductive isolation, diagnosability and monophyly as different criteria. Our theorem statements must make the same distinction. See [de Queiroz (2007), Species Concepts and Species Delimitation](https://pubmed.ncbi.nlm.nih.gov/18027281/).

Let $`H`$ be an admissible history, $`O(H)`$ its observation, and $`S(H)`$ the target. An exact decoder $`d`$ satisfies

```math
d(O(H))=S(H)\qquad\text{for every admissible }H.
```

Such a decoder can exist only if

```math
O(H_1)=O(H_2)\ \Longrightarrow\ S(H_1)=S(H_2).
```

Otherwise the same input would require two different answers. Conversely, constancy on observation fibres lets us define a decoder on observations that actually occur. Extending it to all possible observations also requires an available default output. The repository's existing `ObservationPrediction` formalization records the corresponding recovery criterion under its stated type assumptions. This is an elementary mathematical fact; no novelty is claimed.

This gives a concrete research method: look for histories with the same observable evidence and different target values; if none exist in a specified model, prove why and construct the recovery map.

## Checked negative result: a finite topology does not fix its whole infinite completion

For every finite gARG $`G`$ in the project's Wong model, the existing completion theorem supplies infinite populations $`A`$ and $`B`$ preserving precisely the same raw old edges and ancestry paths. Both satisfy the declared birth-date, finite-past, finite-child, finite-root and connectivity conditions. Yet

```math
\operatorname{Specieslike}(A,V_A),
\qquad
\neg\operatorname{Specieslike}(B,V_B).
```

The new [FiniteGenomeIdentifiability.lean](FiniteGenomeIdentifiability.lean) extracts the direct consequence: no verdict using only $`G`$ correctly decides **whole-population specieslikeness for every topology-compatible completion**. The file's `Compatible` definition specifies that compatibility exactly.

**Verification:** local Lean 4.33.1 compilation passed, exit code zero; three selected theorem endpoints depend only on `propext`, `Classical.choice` and `Quot.sound`. See [verification.json](verification.json). This is a consequence of the already checked completion theorem, with no independent novelty claim for the decoder obstruction.

Here specieslike means the graph conditions in Alexander's proposal: connectedness, convexity, and the **identical ancestor point property (IAP)**. For each member, either its descendants within the set or its nondescendants within the set are finite. The source presents this as a proposed mathematical species framework. See [Alexander (2026), Definitions 1-2](https://arxiv.org/html/2602.05274v1#S2).

The compatible completions in this result are abstract graph completions. They do not extend future genomic interval annotations, infer which organism owns each genome node, or enforce a stochastic model of evolution. The second completion may have proper specieslike subsets even though its whole population is not specieslike. Thus the theorem is neither a universal impossibility theorem for biological species inference nor a proof that genetic data is uninformative.

## Checked positive example: a prescribed law identifies a tree relationship

Allman, Degnan and Rhodes describe a three-taxon coalescent example with one designated rooted species-tree topology $`s`$. Put $`c=e^{-t}`$, where $`t`$ is its internal branch length in coalescent units. Its rooted gene-tree law is

```math
P_{s,c}(g)=
\begin{cases}
1-\dfrac{2c}{3},&g=s,\\[4pt]
\dfrac{c}{3},&g\ne s.
\end{cases}
```

For $`0\le c<1`$, the designated topology exceeds each alternative by $`1-c>0`$. Therefore the exact probability law identifies that topology. The source also states a more general rooted-triple identification theorem. See [Allman, Degnan and Rhodes (2011), Introduction and Proposition 1](https://arxiv.org/html/0912.4472v2#S1).

Our new [ThreeTaxonIdentifiability.lean](positive/ThreeTaxonIdentifiability.lean) checks normalization, nonnegativity in the stated range, the exact gap, the unique maximizer, and identification of both topology and transformed parameter from the prescribed law. At $`c=1`$, it checks that all three entries are $`1/3`$ and no decoder recovers every resolved topology label.

**Verification:** local Lean 4.33.1 compilation passed, exit code zero, with only the three standard axioms listed above. See the [scope and reproduction note](positive/README.md) and [compiler output](positive/validation.txt).

This is a formalization of a known algebraic consequence, not a new biological discovery. The coalescent derivation and exponential substitution are not formalized. The observation is the exact probability law, rather than finitely many loci or raw sequences. The three taxa are already designated: the theorem identifies their relationship, not the boundaries of species. Finite-sample inference requires its own statistical argument.

## What the Wong-Alexander connection currently establishes

| Step | Established result | Remaining assumption or separate question |
|---|---|---|
| Finite genome ancestry representation | An interval-annotated finite DAG, ancestry at a locus, restriction to sample ancestry, and preservation of retained-endpoint ancestry under contraction | Faithful use for a particular biological dataset and any stochastic inference procedure |
| Genome nodes to organism ancestry | A checked path projection under an explicit owner/ancestry compatibility premise | Deriving or validating that biological owner assignment |
| Finite raw topology to infinite populations | Exact old-edge and old-ancestry preservation in contrasting completions | Selecting the actual population or justifying a biological future model |
| Species-related identification | A checked obstruction for unrestricted topology-compatible completions; a separate checked positive tree-law example | A specified model and observation that identify a biologically meaningful species target |

The representation source is [Wong et al. (2024), A general and efficient representation of ancestral recombination graphs](https://doi.org/10.1093/genetics/iyae100). Its data structure and the project's mathematical bridges do not by themselves supply a universal genomic species decoder.

## The useful next theorem

The focused next question is: **which additional assumptions or observations make a specified species target constant across all histories consistent with the evidence?** A positive answer supplies an identification theorem; a counterexample precisely locates missing information.

For Alexander's infinite-population target, restrictions on admissible continuations would need a substantive biological or mathematical justification. For statistical phylogenetics, a useful next result would connect finite observations to an explicit confidence or consistency guarantee under a named model. Neither step follows automatically from the present proofs.

There is a possible later connection to psychology: latent constructs also need explicit observation maps and identification assumptions. That is a research direction, not a consequence establishing a psychological theory, and is outside this mathematical batch.
