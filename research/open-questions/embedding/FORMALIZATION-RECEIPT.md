# Full universal-avoider theorem: checked handoff

25 September 2026. Deliverable for integration: **GenericUniversalAvoiders.lean**. The earlier binary-only `UniversalAvoiders.lean` is a successful local milestone; only the generic module is needed for publication.

## Strongest checked statement

Let P be an infinite edge-labelled Alexander population with actual real birthdates. Its axioms are finite birth sublevels, strictly increasing dates on edges, finitely many children per vertex, finitely many actual parentless roots, a functional label for each edge, and at least one parent of every label at each nonroot. The label type is arbitrary, so every finite nonempty alphabet in the source paper is covered.

For every countable family of such populations, the module constructs a new actual population Q by finite nonempty vertex fibres. It proves all of the following together:

1. Q has exactly the same realized infinite-word language as P.
2. Fibres at original roots have size one; `rootsEquiv` gives a genuine equivalence of the actual root sets.
3. No injective vertex map embeds Q into the underlying undirected graph of any host while preserving edges.
4. The same Q can be chosen to exclude every injective map with any finite global bound on edge stretching, even when that bound depends on the map.

In particular, if P avoids a specified word, so does Q. No candidate countable family is universal for the avoiding class under these embedding notions. Host avoidance is not assumed. Countability and local finiteness of the actual population hosts are derived from their axioms.

The more general `no_countable_host_family` endpoint accepts arbitrary encodable locally finite relational hosts. It does not require host symmetry, label preservation, nonedge preservation or root preservation. Actual undirected population graphs are an explicit specialization.

## What was proved, rather than assumed

- `blowUp` constructs the full population object and discharges every population field.
- `blowUp_language` proves both directions for every infinite label sequence by projection and a section.
- `rootsEquiv` proves root-set equivalence when root fibres are singletons.
- `binaryCover` and `exists_ray` derive a generic unlabelled ray through a two-copy auxiliary binary population and the project's previously checked positive theorem. No input ray is required.
- Finite host balls are recursively constructed from finite neighbour sets.
- Encoding enumerates all host/root-image possibilities. A fibre larger than the relevant finite host ball forces the contradiction.
- Graph powers and a pairing of host/radius indices extend the result to finite global edge stretch.

## Audit names

The final file contains ten explicit fully qualified `#print axioms` commands:

1. `GenericUniversalAvoiders.binaryCover`
2. `GenericUniversalAvoiders.exists_ray`
3. `GenericUniversalAvoiders.no_countable_bounded_stretch_family`
4. `GenericUniversalAvoiders.avoiding_no_countable_bounded_stretch_population_family`
5. `GenericUniversalAvoiders.rootsEquiv`
6. `GenericUniversalAvoiders.blowUp`
7. `GenericUniversalAvoiders.blowUp_language`
8. `GenericUniversalAvoiders.no_countable_host_family`
9. `GenericUniversalAvoiders.no_countable_population_family`
10. `GenericUniversalAvoiders.avoiding_no_countable_population_family`

Each endpoint is required to show only `propext`, `Classical.choice` and `Quot.sound`. The machine-readable receipt records the final compile status and hashes. There are no `sorry`, `admit`, `native_decide`, or custom axiom declarations in the submitted source.

## Reproduction and dependency identity

- Lean: **4.33.1**.
- Mathlib: **0df444a360eaa60ab8c11dca51a86af692955474**.
- Imported project source revision: **425fee8c90e15656caea954ac92beaf28a5d869f**. All 19 transitively imported project source files were compared byte-for-byte against that revision and matched. The shared checkout has other active changes; none were edited by this task.
- The standalone `Check.ps1 -File GenericUniversalAvoiders.lean` uses cached dependency libraries and writes no shared checkout files. The local compiler output is `generic-lean-check.log`.
- Integration should place the module alongside `RealBridges.lean`, add it to the real project's library/build configuration and the audit inventory, then run the publication owner's normal fresh build. This task has not performed that integration or hosted CI.

## Mathematical scope and prior art

The proof does not preserve a prescribed uniform child cap or an exact number of parents per label. It does not settle arbitrary unbounded-stretch topological or ancestry-only embeddings. Fixed-vertex-gender preservation and connectivity are established in the written note but are not separately exposed as checked endpoints in this module.

The underlying graph obstruction is classical: [Lehner's author manuscript](https://www.florian-lehner.net/pdf/universal-locally-finite.pdf) attributes nonuniversality for connected locally finite graphs to de Bruijn via Rado. The population-specific work is verifying that finite-fibre enlargement preserves the exact population axioms, roots and full path language, and then checking the adaptation in Lean. Global novelty and independent human expert review are not established by compilation.

Source question and model: [Alexander, arXiv:1212.0186v2, Definition 1 and Section 6](https://arxiv.org/html/1212.0186v2). Embedding convention: [Cherlin–Shelah, introduction](https://arxiv.org/pdf/math/0512218). The earlier VibeMathed Thue–Morse submission is a separate artifact.
