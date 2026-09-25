# Universal avoiders: separate proof check and bounded-stretch extension

25 September 2026. This task owns the universal-embedding lane; **Explore broader uses for this idea** owns the ordinal lane and coordinates publication. This is a separate AI proof review, not independent human expert review or Lean verification. The existing VibeMathed submission is unchanged.

## Result of the check

I read the complete `UNIVERSAL-AVOIDER-NONEXISTENCE.md` from the coordinating task and rechecked its hypotheses against Alexander's primary paper. I found no mathematical defect in the displayed theorem. Under injective maps preserving graph edges, **no countable family of countable locally finite graphs contains all avoiding populations for a fixed avoidable sequence**. The hosts need not themselves avoid the sequence.

This conclusion adopts an explicit interpretation of the historical question. Alexander's Section 6 does not specify an embedding relation. Subgraph embeddings are a natural interpretation because his cited Cherlin–Shelah comparison uses them by default. It is not an answer to every interpretation of his phrase “to what extent.”

## Checks that matter

| Step | Finding |
| --- | --- |
| Local finiteness of a population | A2 gives finite children. A3 puts every parent in a finite birth sublevel, so parents are finite too. Therefore each undirected finite-radius ball is finite. |
| Countability | The finite sublevels at nonnegative integer thresholds cover every real birthdate, including negative ones. Their countable union contains the vertex set. |
| Rooted infinite ray | A3 prevents infinite backwards ancestry; each vertex descends from a root. Finitely many roots and finite children then give an infinite directed ray starting at a root. Strict birth order prevents repetitions. |
| Finite blow-ups | Replacing each vertex by any finite nonempty set and each edge by all corresponding cross-fibre edges preserves A1–A4 and at least one parent of each gender. Original birthdates can be reused because A3 does not require distinct dates for unrelated vertices. |
| Root count | Set multiplicity one on all roots and enlarge only positive-index vertices of the ray. The root set is preserved in bijection. |
| Exact infinite-word language | Projection of a blown-up path gives a path with the same labels in the original graph. The zero-copy section lifts every original path. Strict original birth order rules out repetition in the projected path. Both inclusions are proved. |
| Diagonal quantifiers | Enumerating every pair of host and possible image of one fixed source root covers every candidate injection. Repetitions handle a finite nonempty enumeration. |
| Contradiction | The entire fibre at ray position k is reachable from that source root in k edges. Its multiplicity exceeds the finite radius-k ball at the selected host vertex, contradicting injectivity. |
| Restricted classes | A fixed child cap or exactly one parent per gender is not preserved. An arbitrary edge-to-path or ancestry embedding need not preserve bounded distances. Those cases require another argument. |

The empty host family and empty host vertex sets present no problem. A connected source remains connected: every vertex of an infinite connected graph has a neighbour, which joins distinct copies within one fibre by a two-edge path.

## A further consequence: even a finite global stretch does not help

The same construction strengthens the negative statement beyond edge-preserving maps. This paragraph is a new deduction in the present check; it is not quoted from Alexander, Cherlin–Shelah, or Lehner.

Fix any Alexander population P and a countable family of countable locally finite undirected hosts U_j. An injective map f from a population into U_j has **global edge stretch at most L** if images of endpoints of every source edge are at undirected distance at most L in U_j, for some positive integer L. L may depend on the map.

Enumerate all triples (j,u,L), where u is a vertex of U_j and L is a positive integer, by positive indices k. As in the original proof choose a directed ray r=v_0,v_1,... in P. For the triple (j_k,u_k,L_k), prescribe

```math
m(v_k)=1+|B_{U_{j_k}}(u_k,L_k k)|,
```

and use multiplicity one off the positive-index ray. All fibres are finite and all roots keep multiplicity one. The same blow-up lemma preserves the population axioms, full infinite-word language, fixed vertex genders when present, and connectivity when present.

Suppose an injective map f into U_j had a global edge-stretch bound L. Choose the enumerated triple (j,f(r'),L), where r' is the unique copy of r. Every vertex of the fibre over v_k is connected to r' by k source edges. The triangle inequality puts all its images in B_Uj(f(r'),Lk). That ball has exactly one fewer vertex than the chosen fibre, contradicting injectivity. Thus a single Q defeats every such map into every listed host, for every finite global stretch bound.

In particular, topological embeddings whose edge-image paths have a uniform finite length bound are obstructed. **Unbounded-stretch topological embeddings and ancestry-only embeddings remain outside this proof.** No assertion about noninjective homomorphisms follows; the projection of Q onto P is itself a label-preserving homomorphism.

## Prior-art assessment

The general graph obstruction is classical. Florian Lehner's *A note on classes of subgraphs of locally finite graphs*, JCTB 161 (2023), 52–62, explicitly attributes the nonexistence of a locally finite universal graph for all connected locally finite graphs to de Bruijn, as reported by Rado. His Theorem 1.1 gives a characterization for closed graph classes and Theorem 3.1 treats general classes with a different condition. We must not present nonuniversality of locally finite graphs as a new discovery.

The population-specific work here is verifying that arbitrary finite fibre multiplicities preserve Alexander's axioms and exact label language, then applying the classical kind of obstruction within the desired avoidance class. A theorem about all locally finite graphs does not automatically imply nonuniversality for an arbitrary subclass, so that preservation argument is necessary. This bounded literature check does not establish worldwide priority for the application or the finite-stretch observation.

## Source anchors and next deliverable

- [Alexander, arXiv:1212.0186v2, Definition 1 and Section 6](https://arxiv.org/html/1212.0186v2): population axioms and historical question, rechecked directly.
- [Cherlin–Shelah, introduction](https://arxiv.org/pdf/math/0512218): weak versus induced universality and their default subgraph convention, rechecked directly.
- [Lehner, author manuscript, 7 February 2023](https://www.florian-lehner.net/pdf/universal-locally-finite.pdf): classical attribution and related universal-host criteria. [Version of record](https://doi.org/10.1016/j.jctb.2023.02.001).

The useful formalization target is a frozen, source-anchored packet containing the finite-fibre construction, population preservation, path-language equivalence, finite-ball lemma, and diagonal theorem. A proof of the last cardinality inequality alone would not certify the population theorem. The active implementation checkout remains owned by the formalization task; this review makes no branch or publication changes.
