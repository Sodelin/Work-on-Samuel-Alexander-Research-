# Older constructions, degree bounds, and rank audit

Review date: 2026-09-25 UTC. Scope: a bounded source challenge to the proposed fixed-gender, outdegree-at-most-three avoidance construction and the proposed rank direction. No shared source files were changed. The calculations below are written mathematical deductions, not Lean-certified results or claims of priority.

## Source findings

Alexander's *Biologically unavoidable sequences*, arXiv:1212.0186v2, defines the fixed-vertex-gender populations `T_h` in Definition 6 and `H_h` in Definition 8. Proposition 11 assumes `h(n) -> infinity`; Proposition 16 additionally requires even values. Corollaries 12 and 17 construct some avoided sequences using those propositions, with Corollary 17 excluding three consecutive identical genders. They do not claim a witness for every prescribed aperiodic target. Section 6 already proposes universal avoiding populations and ordinal classifications, explicitly citing Cherlin--Shelah and Halin/Schmidt. These research directions must be credited to Alexander. [Primary PDF, pp. 4--7 and 9](https://arxiv.org/pdf/1212.0186v2)

The following degree and descendant calculations are **our deductions from the displayed edge definitions**, not propositions quoted from that paper.

## Deduction A: exact outdegrees of the old constructions

**Assumption.** `h(n)` is a positive integer at every generation. Let `q = h(n)`; `m_i^n` and `f_i^n` denote that generation's vertices.

**Conclusion.**

| Construction | Vertex | Outdegree |
| --- | --- | --- |
| `T_h` | `m_1^n`, `f_1^n` | `q + 1` |
| `T_h` | `m_i^n`, `f_i^n`, `i > 1` | `1` |
| `H_h` | `m_1^n` | `q + 1` |
| `H_h` | `m_i^n`, `i > 1` | `1` |
| `H_h` | every `f_i^n` | `2` |

**Counting proof.** In `T_h`, for `q >= 2`, the first male has one next male within its generation, `q-1` daughters within its generation, and the first female of the next generation. The first female is symmetric. Every other vertex has just the next same-gender vertex, crossing to the next generation at the end of its row.

In `H_h`, for `q >= 2`, the first male has `q-1` sons within its generation, the second female of its generation, and the first male of the next generation. Each other male has the next female, crossing generations at the row end. Each female has the next male and female, with both in the next generation at the row end.

**The `q = 1` case is not an exception to the formula.** In either construction, the sole male and sole female each have the next generation's first male and first female as their two children. Thus `q+1=2` remains exact. It would be incorrect to count a nonexistent second vertex within that generation or to double-count one edge.

**Consequence and limit.** The diverging-`h` avoidance arguments have unbounded outdegree. Their stated proofs therefore do not give a uniform cap of three. This is not a proof that no bounded choice of `h`, modified construction, or other older result could yield such a cap. That stronger exclusion has not been established here. Outdegree is the number of children; it is not total undirected degree.

## Deduction B: both old constructions already have cofinite descendants

**Assumption.** Only positivity of `h` is needed; divergence and parity are unnecessary.

**Conclusion.** Every vertex in generation `G_n` is an ancestor of every vertex in `G_k` for all `k >= n+2`. Consequently every vertex's strict descendant set is cofinite, and the entire graph is its unique inspecies.

**Proof for `T_h`.** A male in `G_n` can follow its same-gender row into the first male of `G_(n+1)`. From there it reaches the first female of `G_(n+2)` directly and the first male of `G_(n+2)` by following the male row. The argument starting from a female is symmetric. Having reached both first vertices of a generation, one reaches all its vertices and both first vertices of the next generation. Induction completes the claim.

**Proof for `H_h`.** Every female can follow the female row to its end, which reaches both first vertices of the next generation. A male that is not last in its row reaches the next female of the same generation. A last male reaches the first female of the next generation. In each case, by `G_(n+2)` both first vertices are reachable. Those first vertices reach every vertex of their generation and both first vertices of the next. This also covers singleton generations.

**Proof of the inspecies conclusion.** An infinite ancestrally closed subset `A` must meet the cofinite descendant set of any vertex `x`. Choosing `y` in that intersection forces `x` into `A`. Hence `A` is the entire population. This proves minimality among infinite ancestrally closed sets directly, using the inspecies definition in Alexander's systematic-biology paper. [Definition in Section 4](https://arxiv.org/html/1201.2869)

**Novelty consequence.** Producing *some* fixed-gender avoiding population that is a whole inspecies is already implicit in these older constructions. A defensible comparison for a new construction must focus on the stronger combination of target scope, uniform outdegree bound, explicit construction, and any additional quantitative or formalized properties. This audit supplies no priority certificate for that combination.

## Cherlin--Shelah: related universality question, no demonstrated subsumption

Cherlin--Shelah's Theorem 1 classifies finite trees `T` for which the class of countable undirected `T`-free graphs has a countable universal member: exactly paths and near-paths. Universality is by subgraph embedding, with an equivalent induced-subgraph version in the theorem. The introduction also explicitly distinguishes problems with infinite forbidden graphs and says their methods do not cover those cases. [Author preprint, Theorem 1, p. 3; scope statement, p. 7](https://arxiv.org/pdf/math/0512218)

**Our comparison.** Avoiding a prescribed infinite labelled directed path, while maintaining gender coverage, finite roots, birthdate axioms, and at most three children, is a different theorem statement. A finite unlabelled tree exclusion supplies none of those hypotheses or conclusions automatically. No reduction establishing subsumption was found in this bounded inspection. Even universality among avoiding populations would be a different claim from constructing one avoiding population for each target. Alexander already recognized the analogy in his Section 6.

## Deduction C: two different rank notions must be kept separate

**Setup.** Fix a target word `s` and a starting vertex `v` in a population with finite outdegree. Form the tree `T(v,s)` of finite directed paths starting at `v` whose edge labels agree with the corresponding prefix of `s`. Include the length-zero path as its root.

**Finite-tree conclusion.** This tree is finitely branching. An infinite branch is precisely an infinite realization of `s` starting at `v`. Therefore, if there is no such realization, Konig's lemma implies that `T(v,s)` is finite. Its maximum path length is a natural number. This is a direct compactness consequence, not a newly identified transfinite phenomenon.

**Ordinary well-founded tree height.** With leaves assigned height zero and each node assigned `sup {height(child) + 1 : child is an immediate child}`, each `T(v,s)` has finite height. A superroot attached to the roots for all starts can have height `omega` if those finite heights are unbounded. The superroot is infinitely branching, so there is no conflict with Konig's lemma. No height above `omega` arises from this particular aggregation of finite trees.

**Schmidt/Halin graph rank.** This is a different invariant. Finite graphs have rank zero; higher ranks are assigned by deleting a finite vertex set and inspecting ranks of the remaining components. This definition was checked in Bonato--Bruhn--Diestel--Sprussel, Definition 2, which attributes it to Schmidt and Halin. [Primary research manuscript, Section 2, pp. 2--3](https://www.uni-ulm.de/fileadmin/website_uni_ulm/mawi.inst.081/Henning/raylesstwins.pdf)

**Our resulting rank calculation.** Each finite `T(v,s)` has Schmidt rank zero, regardless of its height. An infinite disjoint union of these finite trees has Schmidt rank one: take the deleted finite set to be empty. Their superroot attachment likewise has Schmidt rank one: delete the superroot. Neither graph is finite, so rank zero is impossible. Thus unbounded finite matching lengths can produce tree-height `omega` while Schmidt rank remains one.

**Interpretation limit.** These ranks concern the matching-path construction. The original population may have many infinite paths with other label sequences; it is not thereby a rayless graph. Applying a rayless-graph rank directly to the population would require a different argument.

## Verification and source-access ledger

| Item | What was inspected | Limitation |
| --- | --- | --- |
| Alexander, arXiv:1212.0186v2 | Full PDF text available; definitions, propositions, corollaries and Section 6 checked directly | Degree/cofinite calculations above are our written deductions, not identified source propositions or checked Lean endpoints |
| Alexander, systematic-biology paper | ArXiv HTML, Section 4 definition | HTML resolves to v7; this audit does not claim a version-by-version textual comparison |
| Cherlin--Shelah | Primary arXiv preprint, definitions, Theorem 1 and stated scope | Rutgers version-of-record PDF request returned an internal error; journal metadata was available, but a full published-text comparison was not completed |
| Halin (1998) | Publisher record and journal archive verify title, pages and DOI | Full article was subscription-gated in the checked route; no claim of direct full-text inspection |
| Bonato--Bruhn--Diestel--Sprussel | Author-hosted primary research manuscript, Definition 2 | Later exposition of Schmidt's rank, not direct access to Schmidt's original dissertation/article |

Halin's verified record is [*The structure of rayless graphs*, 68 (1998), 225--253, DOI 10.1007/BF02942564](https://link.springer.com/article/10.1007/BF02942564). Search-result crawl dates and dynamically printed PDF dates were not treated as original publication dates.

The current audit changes the novelty framing and separates two rank notions. It does not certify global absence of prior art, settle all bounded-`h` variants, or prove the proposed outdegree-three construction.
