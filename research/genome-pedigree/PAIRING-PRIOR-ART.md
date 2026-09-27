# Prior-art review: missing diploid pairing and whole-population IAP

Review date: 2026-09-27. Branch inspected:
`codex/genome-owner-bridge-2026-09-27`. This is a bounded primary-source
literature review, not a proof or compilation receipt. No Lean was run and no
other repository file was edited by this reviewer.

**Verdict:** the distinction between genetic transmission and organism
pedigrees, the use of pairing as additional diploid structure, and pedigree
non-identifiability are established prior mathematics. In the sources examined,
I did **not** locate the candidate's complete conjunction of constraints, or a
theorem that directly implies its opposite-IAP conclusion. The defensible
possible contribution is an explicit constrained construction and its
application to Alexander's IAP. Worldwide priority is not established by this
search.

## Candidate used for the comparison

The observation is the entire infinite realized copy-transmission graph:
vertices `(t,i)` for `t` a natural-number generation and `i` one of eight lanes,
with full-genome transmission only from `(t,i)` to `(t+1,i)`. Coordinates,
times, copy identities, edges, and the initial sampled-copy owners are fixed.
The unobserved structure pairs the eight contemporaneous copies into four
diploid organisms. The proposed pairings are

```text
M0 = (01)(23)(45)(67)
M1 = (12)(34)(56)(70)
M2 = (12)(30)(56)(74).
```

One ownership sequence alternates `M0,M1`; the second agrees for the first two
generations and then alternates `M0,M2`. The intended separation is whole-
population IAP versus failure of IAP, while both organism graphs remain
weakly connected, each organism owns exactly two copies, every nonfounder has
two distinct transmitting parents, and every organism has two children.
Those all-time claims are the implementation lane's proof obligations. The
review below assesses prior-art overlap, not their verification status.

## Targeted source comparison

Page references below are to the linked PDF when available; definition,
theorem, figure and section identifiers provide stable additional locators.

| Primary source and exact locator | Established result or definition relevant here | Comparison with the candidate |
|---|---|---|
| [Wong et al. (2024), *A general and efficient representation of ancestral recombination graphs*](https://doi.org/10.1093/genetics/iyae100), with the [institutional copy](https://eprints.ncl.ac.uk/299415), **Genome ARGs**, p.2; Fig.1, p.3; Appendix D, p.14. | gARG vertices are haploid genomes; interval-labelled edges record realized inheritance. Diploid individuals contain two genomes. The formal node/edge definition is finite and does not contain an organism-pairing function; nodes can carry additional information. Fig.1 displays the organism pedigree separately from its embedded gARG. | Establishes the representation distinction. No constrained pairing-nonidentifiability or IAP theorem was found here. The candidate retains a complete infinite realized graph, so it is an infinite extension of this data interface, not literally one of the paper's finite gARG objects. It must exclude ownership information from the fixed observation. |
| [Thatte, *Reconstructing pedigrees: some identifiability questions for a recombination-mutation model*](https://arxiv.org/pdf/1008.0153v3), **Definitions 2.1–2.2 and Fig.1**, PDF pp.6–7; Theorem 5.13 and Corollaries 5.15–5.16. Published J. Math. Biol. 66 (2013), 37–74, DOI `10.1007/s00285-011-0503-8`. | A diploid pedigree is a sequence-vertex pedigree with a pairing. In that definition, non-extant pairing is determined by shared offspring, while extant pairing is supplied. The underlying sequence pedigree has indegree zero or two: both potential parental sequences are represented. Later results distinguish some previously indistinguishable pedigree examples using recombination/mutation distributions. | This is the closest structural predecessor and an essential qualification. The candidate's realized eight chains each supply only one transmitting predecessor per copy. They omit the second potential homologue arc present in Thatte's model. Consequently the stated pairing-determination observation does not apply to these chains. A claim that pairing is unknowable from **every** haploid-pedigree representation would be false. |
| [Kirkpatrick, *Non-Identifiable Pedigrees and a Bayesian Solution*](https://arxiv.org/pdf/1602.08183), **§2**, PDF pp.3–5; **§4, Fig.2**, pp.11–12; **Theorem 3**, p.10. Expanded 2016 preprint of ISBRA 2012, LNCS 7292, 139–152. | Gives non-isomorphic pedigrees with identical genotype likelihoods for all data and recombination parameters on specified typed individuals, including a three-person example. Its identifiability definition quantifies over input data and parameters. Theorem 3 treats a restricted generational case with necessary edges and leaf labels. | Strong established statistical non-identifiability, but for a different observation map and finite pedigree setting. Equality of one realized full transmission history does not establish equality of these likelihoods; neither implication is supplied here. The candidate's two-copy/two-parent/two-child infinite ownership and IAP conjunction is not stated in this source. |
| [Steel and Hein (2006), *Reconstructing pedigrees: A combinatorial perspective*](https://www.math.canterbury.ac.nz/~m.steel/Non_UC/files/research/Steel_Hein.pdf), **Theorem 2.1**, pp.362–363; **Remark 2.1 and Fig.4**, p.363; **Theorem 3.1**, pp.364–365. | Sex-labelled pairwise subpedigrees determine the ancestral pedigree; dropping the sex-preserving comparison admits a counterexample. A second reconstruction result uses sex-labelled link/lasso information. | Establishes that the supplied labels and observation structure materially change reconstructibility. These inputs are organism subpedigrees or circuit data, not a fixed realized copy graph with unknown pairings. It does not supply the candidate's full-data/IAP separation. |
| [Thatte (2008), *Combinatorics of Pedigrees I: Counterexamples to a Reconstruction Question*](https://epubs.siam.org/doi/10.1137/060675964), with the [author preprint](https://arxiv.org/pdf/math/0609264), **§2.1, Theorem 1**, PDF pp.3–5. | For every order greater than two, constructs non-isomorphic pedigrees with corresponding proper subpedigrees that cannot distinguish them: the stated result is `(n−1)`-hypomorphism. | A strong combinatorial reconstruction failure, but its observation is a family of subpedigrees. It is not a fixed complete realized-transmission graph, and its result does not impose the candidate's ownership, degree and infinite-IAP conditions. This is relevant prior reconstruction work, not an already-proved equivalent. |
| [Matsen and Evans (2008), *To what extent does genealogical ancestry imply genetic ancestry?*](https://matsen.fredhutch.org/papers/matsen2008extent.pdf), **§1 and Fig.1**, pp.182–184; **Proposition 1**, p.184. DOI `10.1016/j.tpb.2008.06.003`. | Separates genealogical descendant counts from descendant-allele counts in a diploid stochastic model. Fig.1 illustrates a genealogical common ancestor without surviving genetic contribution; the paper also establishes conditional expectation results. | Shows that the broad genetic/genealogical distinction is old. The candidate additionally retains every copy and actual transmission, and forbids unwitnessed organism edges. Therefore it is not merely another finite-sample example of a genealogical ancestor leaving no sampled DNA. No opposite-IAP pairing construction was found here. |
| [Alexander (2026), *Specieslike clusters based on identical ancestor points*, v1](https://arxiv.org/html/2602.05274v1), **Definitions 1–4**, §§2–3; **Remark 3**, §3.3. | Defines an infinite biosphere by temporal/local-finiteness conditions, IAP by finite descendants or finite non-descendants within the set, and specieslike clusters by connectivity, IAP and convexity. Maximality is inclusion-maximality among such clusters. | Supplies the exact target predicate. A connected whole population is automatically convex, so the intended IAP contrast also distinguishes whether the whole population is specieslike. This is an application of Alexander's definitions, not a new species definition or evidence that biological species satisfy IAP. No genome-ownership inverse theorem appears in these definitions/results. |
| [Official tskit data model](https://tskit.dev/tskit/docs/stable/data-model.html), **Table Definitions; Node Table; Individual Table**. Software documentation, inspected 2026-09-27. | Node/edge tables encode genetic trees. The optional individual association records which genomes belong to the same organism; individual records can also contain parent IDs. Unspecified node ownership uses the null individual ID. | Directly demonstrates an existing way to preserve the information the candidate withholds. The result cannot be advertised as ambiguity from a fully populated tskit record including those fields. It concerns copy/time/interval information with ownership omitted, except for the specified sampled owners. |

## Novelty verdict and safe statement

**Established before this work:** pedigree reconstruction can fail; genetic
and genealogical ancestry differ; grouping genome copies into individuals is
additional representational structure; and richer labels or probabilistic
observations can change identifiability. Those are not candidate discoveries.

**Potential new deduction or application:** an explicit eight-lane witness
showing that an entire realized transmission history, with the stated degree,
ownership and initial-agreement constraints, need not determine an infinite
organism-level IAP property. The primary sources above do not state that
combined result, and none was found to imply it directly while preserving all
of its constraints. This is a bounded negative search finding, not proof of
priority. Its merit can be the exact strengthened hypotheses and source-faithful
application even if the underlying information-loss mechanism is elementary.

A suitable claim, **once the construction and constraints are proved**, is:

> We give an explicit constrained ownership counterexample: the same complete
> realized copy-transmission graph, dates, genomic coordinates and specified
> initial sampled owners admits two diploid ownership assignments whose
> organism pedigrees differ on whole-population IAP. Both assignments satisfy
> the listed transmission and degree conditions.

Do not replace this with “the first proof that genomes do not determine
pedigrees,” “pedigrees are statistically unidentifiable even with complete
data,” or “Wong ARGs cannot contain individual identity.” These statements
would exceed either the prior-art finding or the candidate's observation map.

Two distinctions must remain visible. First, a **realized** transmission edge
records the homologue that actually contributed material, while a graph of
**potential** parental homologues contains additional reproductive information.
Thatte's pairing rule uses potential predecessor pairs; Wong's interval-labelled
edges record realized contributions, without automatically adding an unused
potential homologue.
Second, two admissible histories giving the same observation are a set-theoretic
inverse obstruction. They do not automatically have equal likelihoods under a
declared recombination/segregation model, or imply failure of almost-sure
statistical identification. An indefinitely prescribed no-recombination,
balanced-transmission history needs its own probability/support analysis if a
stochastic interpretation is claimed.

This review does not duplicate the repository's existing owner-map transfer
theorems or generic counterexamples. It also does not certify the candidate's
mixing bound, tail-family separation, degree counts or infinite-biosphere
conditions. Those are the exact local proof gates for the implementation lane;
the final theorem should cite its checked declarations independently of this
literature review.

## Search boundary

The targeted searches covered Wong's gARG/pedigree interface; haploid/diploid
pairing; pedigree reconstruction and non-identifiability; genetic versus
genealogical ancestry; and Alexander's exact specieslike/IAP definitions.
Representative query phrases were `pedigree gene genealogies identifiability`,
`ancestral recombination graph pairing pedigree`, `Reconstructing pedigrees
identifiability`, and `Non-Identifiable Pedigrees Bayesian`. Citations above
are primary papers, author/institution copies, or official software
documentation. Secondary search results were discovery aids only. The search
did not expand to a full survey of phylogenetic-network identifiability or
collect research datasets.
