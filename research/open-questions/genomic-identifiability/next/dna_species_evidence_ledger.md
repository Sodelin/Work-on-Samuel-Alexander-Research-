# DNA, species, and genealogical graph identifiability

Retrieved 2026-09-25. Bounded primary-literature check for the parent task; not an exhaustive review or proof of novelty. No external writes. The memory registry search for species/Alexander returned no relevant hits.

## Three findings

1. DNA-based assignment to existing named species is established and often effective. Discovering the species partition is a different inference problem. Neither success nor failure of one barcode establishes a universal result about complete genomes.
2. There are rigorous positive and negative identifiability results for explicit evolutionary models. The exact probability law over possible sequence observations is substantially stronger information than one finite realized genome, even if every extant individual is sequenced completely.
3. Genealogical ancestry can persist after all transmitted DNA has disappeared. Alexander already recognizes this boundary and cites Gravel and Steel. It motivates testing the identifiability of his particular graph property; it does not by itself prove that property is unidentifiable.

## Keep the targets and observations explicit

| Target | What is assumed or observed | What an answer would establish |
|---|---|---|
| Assign a sample to a named species | A reference taxonomy/library and diagnostic sequence evidence | Classification relative to those references |
| Delimit species | A set of sampled organisms/populations plus a stated species criterion | A partition or species hypothesis |
| Infer a species/population tree | Given taxon labels plus gene trees/sequences and an evolutionary model | Relationships and sometimes population parameters |
| Recover the pedigree | Extant observations and a mutation/recombination model | An ancestral individual-level graph, usually up to isomorphism |
| Infer reproductive isolation | A stated meaning of isolation, geography/contact, and genetic or mating evidence | Support for a particular reproductive-boundary criterion |

Finite barcode, finite multilocus sample, complete finite extant genomes, and an ideal distribution across arbitrary sequence lengths are four different observation regimes. Identifiability is a property of a specified model-to-distribution map. A shared possible finite outcome does not establish equality of distributions; equality of distributions is the stronger counterexample needed for structural nonidentifiability. Conversely, an identifiable model can still be hard to estimate with realistic data.

## Six core primary sources

### 1. Successful assignment, without a universal delimitation theorem

Hebert PDN, Stoeckle MY, Zemlak TS, Francis CM (2004), **Identification of Birds through DNA Barcodes**. PLoS Biology 2(10):e312. DOI: **10.1371/journal.pbio.0020312**. PMID: **15455034**.

- Full text: https://journals.plos.org/plosbiology/article?id=10.1371/journal.pbio.0020312
- Decisive location: Introduction last two paragraphs and Results first paragraph. In the study's sample, all 260 North American bird species had distinct COI sequences; 130 species had multiple individuals sampled. The study explicitly compared barcode boundaries with prior taxonomy.
- Supports: empirical DNA discrimination of named species, conditional on marker, sampling, and reference taxonomy.
- Limit: not all populations or all species worldwide; not an assay of every reproductive barrier; not a proof that DNA uniquely defines a species partition.

### 2. Population structure versus species boundaries

Sukumaran J, Knowles LL (2017), **Multispecies coalescent delimits structure, not species**. PNAS 114(7):1607-1612. DOI: **10.1073/pnas.1607921114**. PMID: **28137871**.

- Full text: https://pmc.ncbi.nlm.nih.gov/articles/PMC5320999/
- Decisive location: Abstract, Figure 1 explanation, and Results/Discussion. Their simulations place species conversion within a protracted-speciation process; BPP detects isolated lineages without distinguishing completed species from within-species structure.
- Supports: detecting genetic divergence does not automatically settle the biological rank of a lineage.
- Limit: a result about the modeled process and implementations studied, not an impossibility theorem for all possible genomic models or every species criterion. Read with the reply below.

### 3. The competing mathematical interpretation

Leache AD, Zhu T, Rannala B, Yang Z (2019; online 2018), **The Spectre of Too Many Species**. Systematic Biology 68(1):168-181. DOI: **10.1093/sysbio/syy051**. PMID: **29982825**.

- Author full text: https://faculty.washington.edu/leache/wordpress/wp-content/uploads/2020/03/2019SystematicBiology.pdf
- Decisive location: pp.169-170, section Protracted Speciation?, equation (1); pp.179-180 discussion.
- Confirms oversplitting but explains that the simulated species-conversion labels do not enter the sequence likelihood. Conditional on the population tree and parameters, those labels cannot be identified from these sequences. They advocate estimating demographic parameters and applying explicit empirical criteria.
- Limit: this is a conditional nonidentifiability argument. It does not show that every mechanism producing reproductive isolation is genetically invisible. Their alternative approaches still require a species criterion.

### 4. A clear positive tree-identifiability theorem

Allman ES, Degnan JH, Rhodes JA (2011; online 2010), **Identifying the rooted species tree from the distribution of unrooted gene trees under the coalescent**. Journal of Mathematical Biology 62:833-862. DOI: **10.1007/s00285-010-0355-7**. PMID: **20652704**.

- Author full text: https://www.cs.uaf.edu/~jrhodes/papers/STfromUnrootedGTs.pdf
- Decisive location: Theorem 9, PDF p.18; notation on PDF p.6. Under the multispecies coalescent, the exact distribution of unrooted gene-tree topologies with one lineage per given taxon identifies the rooted topology and internal lengths for at least five taxa. With four, it identifies only the unrooted metric tree. Lengths are in coalescent units; pendant lengths are excluded in this one-lineage setting.
- Limit: given taxon labels, explicit model, and exact distribution. This is not a theorem delimiting species or recovering an entire individual pedigree from one genome.

### 5. The direct genealogy/genetics distinction already cited by Alexander

Gravel S, Steel M (2015), **The existence and abundance of ghost ancestors in biparental populations**. Theoretical Population Biology 101:47-53. DOI: **10.1016/j.tpb.2015.02.002**. PMID: **25703300**.

- Author full text: https://www.math.canterbury.ac.nz/~m.steel/Non_UC/files/research/ghosts.pdf
- Decisive location: Proposition 2.1, p.48. For the random biparental model with generations of size N and the stated recombination model, the probability of a super-ghost within c log2(N) generations tends to one as N grows, for any c>1. A super-ghost is a genealogical ancestor of every extant individual but genetic ancestor of none.
- Limit: probabilistic result under a particular pedigree/recombination model; not universal species nonidentifiability. Proposition 2.2 has an ordered limit and finite-base-pair assumption; do not interchange those limits.

### 6. A directly relevant positive, partial pedigree result

Thatte BD (2013; online 2012), **Reconstructing pedigrees: some identifiability questions for a recombination-mutation model**. Journal of Mathematical Biology 66(1-2):37-74. DOI: **10.1007/s00285-011-0503-8**. PMID: **22246066**.

- Author preprint full text: https://arxiv.org/pdf/1008.0153 ; record: https://pubmed.ncbi.nlm.nih.gov/22246066/
- Decisive location: Theorem 5.13, preprint p.28; Section 6, pp.35-36. For finite pedigrees with equal arc counts, fixed mutation parameter in (0,1/|Sigma|), and sufficiently small crossover probability, equality of alignment distributions for every length implies equality of specified spanning-forest sequence counts.
- Limit: partial identifiable invariants, not a general full-reconstruction theorem. The discussion explicitly leaves completeness/converse and practical estimation bounds open. This is relevant prior art for asking whether a particular specieslike invariant is recoverable even if the entire graph is not.

## Narrow supporting checks

**Genomic heterogeneity and gene flow.** Poelstra JW et al. (2014), *The genomic landscape underlying phenotypic integrity in the face of gene flow in crows*, Science 344:1410-1414, DOI **10.1126/science.1253226**, PMID **24948738**. Full text: https://www.reed.edu/biology/courses/BIO431S05_2017/2017_papers/Poelstra_2014.pdf . Abstract and p.1411: extensive genome-wide introgression coexists with phenotypic differentiation; one region under 2 Mb contains 81 of 82 fixed differences among 8.4 million SNPs examined. This challenges a simple uniform genomic-distance account, without proving DNA cannot classify these crows or resolving every species concept.

**Positive and negative results depend on observation model.** Thatte BD, Steel M (2008), *Reconstructing pedigrees: A stochastic perspective*, Journal of Theoretical Biology 251(3):440-449, DOI **10.1016/j.jtbi.2007.12.004**, PMID **18249415**. Full text: https://www.math.canterbury.ac.nz/~m.steel/Non_UC/files/research/pedigree3.pdf . Proposition 1 constructs indistinguishable nonisomorphic pedigrees under a symmetric two-state i.i.d. model. Theorem 1 gives recovery for a specially constructed automaton when sequence length and alphabet size are sufficiently large. It is not a general fixed four-letter DNA theorem.

**Recent progress still states criteria.** Kornai D et al. (2024), *Hierarchical Heuristic Species Delimitation Under the Multispecies Coalescent Model with Migration*, Systematic Biology 73(6):1015-1037, DOI **10.1093/sysbio/syae050**, PMID **39180155**. Full text: https://academic.oup.com/sysbio/article/73/6/1015/7740481 . The Discussion's Challenges and Utility section explicitly discusses ambiguity even with a complete demographic history; its genealogical-divergence thresholds are heuristics. Chambers EA et al. (2025), *Distinguishing species boundaries from geographic variation*, PNAS 122(19):e2423688122, DOI **10.1073/pnas.2423688122**, full text https://pmc.ncbi.nlm.nih.gov/articles/PMC12088384/ , provides a successful genomic/landscape workflow for leopard frogs. These are evidence of active conditional progress, not evidence that no future general theorem is possible.

## Concrete research target, explicitly our inference

Let H be an admissible genealogical history, F(H) the specific Alexander specieslike structure being investigated, and P_H the observation law under a specified genomic process. The useful question is whether P_H=P_H' implies F(H)=F(H'). A positive answer can hold even when H itself is not identifiable. A negative result needs two admissible histories with equal observation laws but different F values. Merely changing invisible ancestral details does not suffice if those changes leave F invariant.

Start with a finite, clearly defined restriction or approximation of the target graph property and explicit mutation/recombination/sampling assumptions. If the target uses infinite descendants or future history, state that additional bridge rather than silently treating an extant genome as the entire graph. This is a research formulation, not a claimed novel theorem. The Thatte literature must be checked before claiming novelty for it.

Search scope found no universal theorem saying that complete DNA uniquely determines every biological species partition. This bounded search cannot certify the absence of one. The positive results above establish known conditional targets; the delimitation debate prevents calling the broad, unspecified question solved.

## Metadata, version, and correction check

PubMed verified Hebert PMID15455034, Allman PMID20652704 (2011 Jun;62(6):833-862; online 2010-07-23), Leache PMID29982825 (2019 Jan;68(1):168-181), and the other identifiers given above. Thatte2013 full-text theorem references are to arXiv:1008.0153v3, submitted 2011-09-06, whose arXiv record links the 2013 journal reference and DOI. The author's 2008 and 2015 PDFs have journal metadata; no abstract-only theorem was promoted to a full-text finding. Narrow PubMed correction/erratum/retraction queries for the principal DOIs surfaced no relevant correction or retraction. This is a bounded notice check, not a comprehensive Crossmark or retraction audit. A related Hebert commentary surfaced (Moritz and Cicero, 2004, DOI10.1371/journal.pbio.0020354, PMID15486587); PubMed labels it CommentOn, not a correction. Chambers2025 PMID is 40324080.
