# No universal avoiding population under graph embeddings

Research note, 25 September 2026. The complete generic population construction and nonuniversality theorem, including the finite global edge-stretch extension, are now checked locally in Lean 4.33.1 in [GenericUniversalAvoiders.lean](GenericUniversalAvoiders.lean), with ten audited endpoints. This note records local completion before publication; the exact-commit hosted result is recorded in [PR #6 checks](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/pull/6/checks). The written proof was also reviewed by a separate AI task; independent human expert review and worldwide priority are not established. The general locally finite graph obstruction is classical (de Bruijn, reported by Rado; see Lehner below). The population-specific formalization checks preservation of Alexander's axioms, actual roots and entire infinite-word language. [Section 8](#8-lean-formalization-and-verification-status) maps the checked endpoints and remaining scope boundaries.

## Source question and interpretation

Samuel Alexander, *Biologically Unavoidable Sequences*, arXiv:1212.0186v2, Section 6, printed p. 9, asks:

> If s is an avoidable gender sequence, to what extent can we find populations avoiding s which are universal among all such, in a way analogous to that described by Cherlin and Shelah [5]?

This wording was verified against the supplied local PDF `J:/Games/1212.0186v2.pdf`. The [public paper](https://arxiv.org/pdf/1212.0186v2) supplies the same statement. Alexander does not define an embedding relation in this question. In the cited [Cherlin–Shelah paper, Introduction, p. 293](https://sites.math.rutgers.edu/~cherlin/Paper/2007ForbiddenTree.pdf), weak universality means containing every member as a subgraph, and strong universality means containing every member as an induced subgraph. They use the weak meaning by default.

For this note an adjacency embedding is an injective vertex map preserving every edge of the underlying undirected graph. It need not preserve nonedges, directions, labels, roothood, ancestry, or birthdates. Impossibility for this weak requirement implies impossibility for the usual directed or labelled subgraph embeddings and all the stronger variants just listed.

Fix a positive number n of genders and a sequence s over those genders. Let C_s be Alexander's infinite n-gendered populations that avoid s. The natural single-universal question is

```math
\exists U\in C_s\ \forall P\in C_s\ \exists f:P\hookrightarrow U.
```

Here s is assumed avoidable, so C_s is nonempty. The result below gives a negative answer to this interpretation and rules out countable universal families as well.

## Theorem

**Let P be any Alexander population. For every countable family (U_j) of countable locally finite undirected graphs, there is an Alexander population Q such that:**

1. **Q has exactly the same set of realized infinite gender sequences as P.**
2. **The actual roots of Q are in a canonical bijection with the roots of P.**
3. **The underlying undirected graph of Q admits no adjacency embedding into any U_j.**

The written construction also preserves permanent vertex genders when they give the edge labels, and preserves undirected connectivity when P is connected. These two additional properties are argued below; they are not separately exposed as checked endpoints in the current Lean module.

Consequently, for every biologically avoidable s, C_s has no weak universal member, no strong universal member, and no countable family of members into which all members embed. The same negative statement holds even when potential hosts are permitted to realize s, provided that they remain countable and locally finite.

## 1. Population preliminaries

Write P=(V,E,t,g), with g assigning one of the n genders to each directed edge. Its axioms are: finitely many actual parentless roots; finitely many children per vertex; strictly increasing birth time on edges and finitely many vertices born by every real threshold; infinitely many vertices; and a parent of every gender for each nonroot.

Every vertex has finitely many parents: all its parents occur in the finite birth sublevel at its birth time. Together with finite child sets, this makes the underlying undirected graph locally finite. Every finite-radius ball in such a graph is finite, by induction on the radius.

The vertex set V is countable, since it is the union over natural k of the finite sets {v:t(v)<=k}. No vertex has an infinite chain of ancestors: all vertices in any such chain would belong to its finite birth sublevel. Therefore every vertex descends from a root.

There is an infinite directed ray

```math
r=v_0\longrightarrow v_1\longrightarrow v_2\longrightarrow\cdots
```

starting at an actual root. Indeed, some root has infinitely many descendants because there are only finitely many roots. At a vertex with infinitely many descendants, one of its finitely many children has infinitely many descendants. Iterating gives the ray. Strict birth order ensures that the v_i are all distinct and that v_i is not a root for i>=1.

## 2. Finite-fibre blow-up lemma

Choose any function m:V→{1,2,3,...}. Replace each v by the finite nonempty fibre

```math
F_v=\{(v,a):0\leq a<m(v)\}.
```

Define Q_m to have vertex set the disjoint union of these fibres. For every original edge v→w, include all edges

```math
(v,a)\longrightarrow(w,b),\qquad a<m(v),\quad b<m(w),
```

and give each this original edge's label g(v,w). Add no other edges. Give (v,a) birth time t(v).

All population axioms hold:

- **Roots:** (v,a) is parentless exactly when v is parentless. Thus there are only finitely many roots, since the original root set is finite and each root fibre is finite. If m=1 on roots, the root set is preserved exactly.
- **Children:** the children of (v,a) form the union of F_w over original children w of v. This is a finite union of finite sets.
- **Birth order:** each new edge projects to an original edge, so its birth times strictly increase.
- **Finite birth sublevels:** the new sublevel at time T is the union of F_v over original vertices with t(v)<=T. Again this is a finite union of finite sets. Equal birth times among copies do not violate Alexander's axioms.
- **Infinitude:** the canonical section v↦(v,0) injects the original infinite vertex set into Q_m.
- **Every parent gender:** if (w,b) is a nonroot and c is a gender, choose an original c-labelled parent v of w. Then (v,0) is a c-labelled parent of (w,b).

Let L(P) denote the set of all infinite edge-label sequences realized by directed paths starting anywhere in P. Projection π(v,a)=v maps every directed path in Q_m to a directed path in P with the same labels. Its vertices cannot repeat, since their original birth times strictly increase. Conversely, the canonical section v↦(v,0) lifts every directed path in P to one in Q_m with the same labels. Therefore

```math
L(Q_m)=L(P).
```

In particular Q_m avoids s whenever P avoids s. This is stronger than preservation of one forbidden sequence.

If labels come from permanent vertex genders γ(v), give each (v,a) gender γ(v). The construction then has the same fixed-gender interpretation. If P is weakly connected and infinite, every original vertex has a neighbor. Paths between different fibres lift from P; two different copies of the same vertex are joined by a two-edge undirected path through any neighboring fibre. Thus Q_m is weakly connected.

## 3. Diagonal construction against a countable family

Consider every possible pair (j,u) consisting of a candidate host index j and a vertex u in U_j. This is a countable set. If it is empty, any Q_m works. Otherwise list it as

```math
(j_1,u_1),(j_2,u_2),\ldots,
```

with every pair appearing at least once; repetitions are allowed. A finite nonempty set can be listed by repetition.

Let B_{U_j}(u,k) denote the undirected ball of radius at most k around u in U_j. Define multiplicities along the ray from Section 1 by

```math
m(v_k)=1+|B_{U_{j_k}}(u_k,k)|\quad(k\geq1),
```

and set m(v)=1 for every vertex not among v_1,v_2,.... All these positive integers are finite. The ray vertices are distinct, so the prescription is consistent. In particular m=1 on every root.

Let Q=Q_m and let r'=(r,0). For each k>=1, every vertex in F_{v_k} is connected to r' by the directed path of length k that takes copy 0 at all intermediate ray vertices and the chosen copy at the final vertex. Thus

```math
F_{v_k}\subseteq B_Q(r',k).
```

Suppose an adjacency embedding f:Q→U_j existed. Its root image f(r') is some u in U_j, so choose k with (j_k,u_k)=(j,u). The image of every length-k source path is a length-k target path. Consequently f sends the m(v_k) distinct vertices of F_{v_k} into B_{U_j}(u,k). Injectivity gives

```math
1+|B_{U_j}(u,k)|=m(v_k)\leq |B_{U_j}(u,k)|,
```

a contradiction. Hence Q embeds into none of the U_j. This proves the theorem.

The construction uses one source population and changes only finite multiplicities. It does not add countably many independent roots or an infinitely branching vertex. Those would violate the population axioms; this construction does neither.

## 4. Scope of the negative answer

The formal nonuniversality result covers the embedding obstructions, full language and actual root-set equivalence. The connectivity and permanent-vertex-gender refinements below retain their written-proof status.

| Formulation | Consequence and reason |
|---|---|
| Weak graph universality in the sense of the cited Cherlin–Shelah paper | Impossible, even after forgetting directions and labels. |
| Strong / induced graph universality | Impossible, since an induced embedding is also an adjacency embedding. |
| Directed, edge-labelled, or permanent-vertex-gender-preserving embedding | Impossible, since each such embedding induces an adjacency embedding. |
| Embeddings that also preserve birthdates, roots, or a distinguished root | Impossible by the stronger obstruction already proved. |
| Fixed finite number of biological roots | For every nonempty class with a witness P having that root count, the construction preserves that same count and defeats every countable family of hosts. |
| Weakly connected populations | Choose an infinite weak component of any avoiding population as P. Such a component exists because every component contains a root and there are finitely many roots; it inherits all axioms and avoidance. Its blow-up stays connected. Thus connected avoiders also have no countable universal family. |
| Connected populations with a marked biological root | Choose the root r at the beginning of the ray and mark it. The same construction works, even against embeddings that need not respect the mark. |
| Exactly one biological root when n>=2 | This is not the relevant connected/rooted interpretation: such a simple n-gendered infinite population cannot exist. The earliest nonroot needs distinct parent vertices for the n labels, all of which must be roots. Thus there must be at least n biological roots. |
| The class with exactly the same entire infinite path language as one P | Still no countable universal family: every constructed Q has L(Q)=L(P). |

For the minimum-root observation in the table, an earliest nonroot exists because birth sublevels are finite. Every parent of it must be a root. A single original edge has only one label, so n different required parent labels require n distinct parent vertices. This is an observation about Alexander's simple edge-labelled graph convention; allowing parallel differently labelled edges would change it.

## 5. What is not settled by this proof

The original question is phrased broadly as “to what extent,” so a result for standard graph embeddings should not be advertised as an answer to every possible weakened category. In particular:

- **Arbitrary noninjective graph homomorphisms:** the cardinality argument uses injectivity. Indeed, every Q_m has a natural label-preserving homomorphism onto P.
- **Arbitrary topological embeddings or ancestry-only embeddings:** an original edge may map to a path of unbounded length. The fixed-radius argument does not apply to that category. The bounded-stretch extension below does rule out every injective map with any finite global bound on edge-image lengths.
- **A prescribed uniform upper bound on children, or an exact number of parents per gender:** finite blow-ups preserve local finiteness and at-least-one-parent-per-gender, but not a fixed degree cap or uniqueness of parents. Those are separate restricted-class questions.
- **Uncountable universal families or hosts outside local finiteness:** the theorem gives no positive construction and no exact universality cardinal for these changes of scope.

The displayed theorem and the bounded-stretch extension now have complete local Lean proofs in the accompanying standalone module. Their connection to the source question depends on explicitly adopting the stated embedding category; ordinary subgraph embeddings are the default notion used by Alexander's cited comparison. The module is published beside this note and is selected by the research-artifact auditor after the existing library build. It is not added to the main real-library endpoint aggregate, and the exact-commit hosted result is recorded separately in PR #6 checks.

Nonuniversality via finite neighborhood growth is a classical kind of obstruction for locally finite graph classes. Applying the finite-fibre lemma to Alexander's particular class gives a concrete negative answer to this population question; it does not, by itself, establish a new general result in graph theory or worldwide priority.

## Review checklist

- Countable enumeration covers every possible image of one fixed source root in every candidate host.
- The obstruction uses k>=1, so all multiplicities on actual roots remain 1.
- No global degree bound is assumed or asserted.
- Each individual multiplicity is finite, even though the multiplicities may be unbounded over V.
- Exact path-language equality follows from both projection and section, not from an informal avoidance analogy.
- Injectivity is used only at the final finite cardinality contradiction.
- Weak connectivity is distinct from having exactly one biological root.
- Host local finiteness follows from both A2 and A3 when hosts are Alexander populations.

## 6. Bounded-stretch extension (also checked in Lean)

The same negative conclusion holds if an injective vertex map may send adjacent vertices to points at distance at most a positive integer L, with one finite L applying to the entire map. L may depend on the map; no common bound across all maps is assumed. This extension was developed during the separate review and is now checked by `GenericUniversalAvoiders.no_countable_bounded_stretch_family`, together with its actual-population specialization. It is not attributed to the cited sources, and no worldwide novelty claim is made.

Enumerate every triple (j,u,L), with u in host U_j and L a positive integer, by positive indices k. Using the same source ray, replace the earlier multiplicity by

```math
m(v_k)=1+|B_{U_{j_k}}(u_k,L_k k)|.
```

All multiplicities remain finite and every biological root keeps multiplicity one. Thus all preservation conclusions of Section 2 still hold. For any purported injective map f into U_j with edge stretch at most L, choose k enumerating (j,f(r'),L). Each vertex of the fibre over v_k is joined to r' by a source path of length k. Its image lies in the host ball of radius Lk, by the triangle inequality. The fibre is one vertex larger than that ball, contradicting injectivity. The same Q therefore defeats every such map into every listed host.

This includes topological embeddings whose edge-image paths have a uniform finite length bound. It does not settle arbitrary unbounded-stretch topological embeddings or ancestry-only embeddings. The construction also does not preserve a prescribed child cap or exact number of parents per gender.

## 7. Classical context and source anchoring

Florian Lehner, *A note on classes of subgraphs of locally finite graphs*, Journal of Combinatorial Theory, Series B 161 (2023), 52–62, attributes nonexistence of a universal member for all connected locally finite graphs to de Bruijn, as reported by Rado. See the [author manuscript, page 2](https://www.florian-lehner.net/pdf/universal-locally-finite.pdf#page=2) and [version of record](https://doi.org/10.1016/j.jctb.2023.02.001). Lehner gives universal-host criteria for closed graph classes (Theorem 1.1) and a more general criterion (Theorem 3.1). The general graph obstruction must not be advertised as new.

A theorem about the full class of locally finite graphs does not automatically imply the same theorem for an arbitrary subclass. For Alexander's avoidance classes, the specific step established here is closure under finite-fibre blow-ups while preserving exact infinite-word language and biological root count. This supplies the necessary population-specific construction. This bounded check does not certify worldwide novelty of that application or of the finite-stretch strengthening.

The source axioms were rechecked against [Alexander, Definition 1](https://arxiv.org/html/1212.0186v2), and the weak/strong convention against [Cherlin–Shelah, introduction](https://arxiv.org/pdf/math/0512218). The completed local Lean proof now includes the full blow-up population object, population preservation, exact language equivalence, actual-root equivalence, a derived ray, and the diagonal obstruction. The interpretation of the source question and any novelty assessment remain separate from kernel verification.


## 8. Lean formalization and verification status

The accompanying [GenericUniversalAvoiders.lean](GenericUniversalAvoiders.lean) formalizes a generic `Population V Label` with arbitrary vertex and label types and actual real birthdates. The fields are infinitude, finite birth sublevels, strict birth order on edges, a unique label for each ordered vertex pair, finitely many parentless roots, finitely many children per vertex, and a parent of each label for every nonroot. Every finite nonempty gender alphabet from Alexander's source model is included. The formalization is not restricted to binary labels or to vertices initially identified with natural numbers.

The selected audit prints ten fully qualified endpoints, all with only the permitted standard axioms `propext`, `Classical.choice` and `Quot.sound`:

| Checked endpoint in `GenericUniversalAvoiders` | Content |
|---|---|
| `binaryCover` | Builds the auxiliary two-copy binary population from the generic population and discharges its fields. |
| `exists_ray` | Derives an injective directed ray; a ray is not assumed as input to the nonuniversality theorem. |
| `blowUp` | Constructs the complete population with arbitrary positive finite fibre sizes. |
| `blowUp_language` | Proves equality of the entire realized infinite-word language, by projection and section. |
| `rootsEquiv` | Gives a genuine equivalence of actual root sets when original root fibres have size one. |
| `no_countable_host_family` | Defeats every countable family of encodable locally finite relational hosts by an actual population blow-up. |
| `no_countable_population_family` | Specializes to actual population hosts and derives their countability and local finiteness from their axioms. |
| `avoiding_no_countable_population_family` | Preserves avoidance of a specified word and excludes every injective adjacency-preserving map into the candidate population family. |
| `no_countable_bounded_stretch_family` | Produces one population excluding every injective map into every listed host with any finite global edge-stretch bound. |
| `avoiding_no_countable_bounded_stretch_population_family` | Combines word avoidance, full language equality, singleton root fibres, and the finite-stretch obstruction for actual population hosts. |

The formal proof derives a ray starting at some vertex; the start need not be a root. This is sufficient because only positive-index ray vertices have enlarged fibres, and each such vertex has an incoming ray edge and is therefore not a root. The written proof above uses a root-starting ray, which is a convenient stronger choice. Both constructions preserve every actual root fibre as a singleton.

The general host theorem assumes an encoding for each host vertex type and finite neighbour sets. For the actual-population corollaries, both properties are derived. Host avoidance, preservation of labels or directions, preservation of nonedges, and preservation of roots are not required of the forbidden maps. The finite-stretch result uses graph powers to include every natural-number stretch bound in the diagonal family; the bound may depend on the proposed map.

### What the current check establishes

- The frozen generic module compiled locally using Lean **4.33.1** and the pinned Mathlib revision **0df444a360eaa60ab8c11dca51a86af692955474**.
- All ten selected endpoint axiom reports passed. These standalone research endpoints are separate from the registered core and real-library endpoint totals.
- The module lives beside this research note. The research-artifact auditor compiles it using the existing built project dependencies; it is not placed among the main `real` library modules.
- The exact-commit hosted result is recorded in PR #6 checks. A successful earlier library CI run does not certify this newly added module.
- Compilation establishes the formal statements. The source-model comparison above, biological interpretation and independent human expert review remain distinct.

After the existing core and real-library build/audit steps, the selected research artifacts can be checked with:

```sh
python3 checks/audit_research_artifacts.py --output verification/research-artifacts.json
```

### Remaining category boundaries

Connectivity and permanent-vertex-gender preservation remain written extensions, without separate checked endpoints in this module. The theorem does not preserve a prescribed uniform child cap or exact parent counts. It does not settle embeddings with arbitrary unbounded edge stretch, arbitrary ancestry-only embeddings, or noninjective maps. These are changes of mathematical category, not omitted steps in the checked adjacency and finite-global-stretch theorems.
