**Universal-avoider embedding audit and exact-parent strengthening — 29 September 2026**

The existing nonuniversality result survives this audit under its stated category: injective adjacency-preserving maps, and more generally injective maps with an arbitrary finite global edge-stretch bound. The checked statement is stronger than absence of a single universal avoider: no countable family of actual population hosts suffices. A new construction now removes the old method's restriction concerning exact incoming parent counts. These are mathematical and local Lean results; independent human review and worldwide priority have not been established.

**Source interpretation.** Alexander's Section 6 asks how far universal avoiding populations can be obtained, without specifying an embedding relation. Definition 1 permits vertices with no children and permits equal birthdates when no edge joins the vertices; its positive parent requirement concerns every label at each nonroot. These details are material to the new construction. [Alexander, arXiv:1212.0186v2, Definitions 1–2 and Section 6](https://arxiv.org/html/1212.0186v2)

The actual cited Cherlin–Shelah publication defines weak universality by containment as a subgraph and strong universality by induced-subgraph containment, using the weak convention by default. Thus ordinary injective subgraph embeddings are a well-supported reading of Alexander's comparison. That interpretation does not automatically answer a separate question about arbitrary subdivisions or ancestry relations. [Cherlin–Shelah, JCTB 97 (2007), printed p. 293](https://sites.math.rutgers.edu/~cherlin/Paper/2007ForbiddenTree.pdf)

Nonuniversality for the full class of connected locally finite graphs is classical: Lehner attributes it to de Bruijn via Rado. The population-specific burden is to stay inside the same avoidance class while creating the needed finite neighbourhood growth. The new terminal-clone construction, like the older complete blow-up, supplies that closure argument. This audit does not claim a new general graph-theory obstruction. [Lehner, author manuscript, p. 2](https://www.florian-lehner.net/pdf/universal-locally-finite.pdf)

**Audited material and fresh check.** The frozen existing sources are:

- [UNIVERSAL-AVOIDER-NONEXISTENCE.md](C:/Users/Owner/Documents/Codex/2026-09-27/wong-alexander/research/open-questions/embedding/UNIVERSAL-AVOIDER-NONEXISTENCE.md), SHA256 `75DC49CF0AF65EEFFE23C008B009B63529E463BE76DD64E73C92517378761C76`.
- [GenericUniversalAvoiders.lean](C:/Users/Owner/Documents/Codex/2026-09-27/wong-alexander/research/open-questions/embedding/GenericUniversalAvoiders.lean), SHA256 `7C96183BD1CEA8A694B59A12DEF6EBEDB2B6F238044A6C6FB24610E49A37EAC4`.

A byte-identical copy of the generic module was compiled in this scratch directory. All ten selected endpoints reported only `propext`, `Classical.choice`, and `Quot.sound`. The fresh compiler receipt is [GenericUniversalAvoiders.check.json](C:/Users/Owner/Documents/Alexander-Open-Questions-2026-09-29/embedding/GenericUniversalAvoiders.check.json).

The owning GitHub checkout, `C:/Users/Owner/Documents/GitHub/Work-on-Samuel-Alexander-Research-`, was at commit `425fee8c90e15656caea954ac92beaf28a5d869f` when inspected. Its current files did not contain the generic module or the nonexistence note by name/content. Consequently this report identifies the actual frozen source rather than asserting that the material is already present in that checkout. No hosted-CI or publication claim was freshly verified.

**Attempted falsifications of the existing theorem.**

| Potential failure | What the actual statement/proof does |
|---|---|
| Countability silently assumed for population hosts | `populationEncodable` derives an encoding from birth-order enumeration. A finite birth sublevel exists at each real threshold; their union over natural thresholds covers every vertex. |
| Parent sets might be infinite | Every parent precedes the child's birthdate, hence lies in one finite birth sublevel. Together with finite children this proves undirected local finiteness in `populationHost`. |
| A ray is an extra hypothesis | `exists_ray` derives it through the checked binary cover and positive theorem. No ray argument is supplied by the caller of the nonuniversality theorem. |
| The formal ray does not start at a biological root | Correct, but harmless. Only positive-index ray vertices receive enlarged fibres; each has an incoming ray edge, hence is not a root. The enumeration covers every possible image of the anchor vertex, whether rooted or not. |
| “Realizes” permits repeated vertices | It is stated as a legal infinite edge sequence; chronological birthdates force every such sequence to be injective. Thus the language statement has the intended directed-ray meaning. |
| More than one forbidden word might be created | Projection and the canonical section prove equality of every realized infinite word for the complete blow-up. Avoidance is a corollary, not an unproved assertion. |
| Root count might mean only a numerical bound | `rootsEquiv` gives an equivalence of the actual parentless-vertex sets, assuming singleton root fibres. The diagonal construction proves that assumption. |
| The diagonal misses a host vertex or depends on an alleged embedding | Encoding every pair (host index, anchor image) supplies a specific obstructing fibre. Multiplicities are defined before the map is quantified. |
| The stretch bound must be shared by all maps | The theorem has one existential population followed by universal quantifiers over host, natural stretch bound, and injective map. It uses all finite graph powers in one countable diagonal family. |
| Local finiteness is replaced by a uniform degree bound | No uniform degree bound is asserted. Each individual multiplicity and each finite-radius ball is finite; the sequence of multiplicities can be unbounded. |

The relevant existing endpoints are `GenericUniversalAvoiders.Population` (line 31), `blowUp` (85), `blowUp_language` (113), `exists_ray` (208), `no_countable_host_family` (303), `populationHost` (334), `populationEncodable` (348), `avoiding_no_countable_population_family` (367), `rootsEquiv` (382), and `avoiding_no_countable_bounded_stretch_population_family` (434). The underlying finite-cover and infinitude definitions in `lean/SamuelAlexanderResearch/BirthOrder.lean` and the actual real-birthdate model in `real/RealBridges.lean` were also inspected. No hidden degree cap, fixed root, root-preservation requirement on embeddings, or avoidance requirement on the hosts was found.

**New checked construction: terminal clones preserve incoming parent sets.**

Given a population P and positive finite multiplicities m(v), replace v by (v,a), 0 ≤ a < m(v), retaining its birthdate. Replace an original labelled edge v → w by precisely the edges

```text
(v,0) → (w,b),  for every b < m(w),
```

with the original label. Only canonical copies can have children. Each clone of w has exactly the original incoming parents, each represented by its canonical copy. Thus, separately for every label c,

```text
{parents of (w,b) with label c}  ≃  {parents of w with label c}.
```

This is a genuine Lean equivalence, `incomingParentEquiv`, not merely a cardinality assertion. In particular, exact-one-parent-per-label populations remain exact-one-parent-per-label populations.

The full population axioms hold: roothood is unchanged by projection, children are contained in finitely many finite fibres, chronology follows from P, each birth sublevel is a finite union of finite fibres, the canonical section proves infinitude, and the prescribed parents are present. A noncanonical clone has no children, which Alexander's model permits. Projection of paths and lifting by the canonical section prove exact equality of the entire infinite-word language. Taking m = 1 on the original roots gives a canonical equivalence of actual root sets.

The same diagonal still works. Along an injective ray v0 → v1 → …, every copy of vk is reached in exactly k steps using canonical copies until the final edge. Enumerate candidate host/anchor pairs at positive indices k and choose m(vk) one larger than the corresponding host ball of radius k. An injective edge-preserving map would place this oversized fibre inside that ball. Including all graph powers of all hosts handles every finite global stretch bound at once. The stretch may vary between maps; no one global bound across maps is required.

**Reduction from any avoider to exact parents.** For every original nonroot and label, choose one existing parent of that label and delete the other incoming edges. This keeps the same vertex set, birthdates, actual roots, infinitude and finite-child property, while producing exactly one parent of each label. Every surviving path was an original path, so avoidance is preserved. The word language may shrink at this selection step. Terminal cloning then preserves the selected population's language exactly.

The strongest checked endpoint is:

```text
TerminalCloneAvoiders.avoiding_no_countable_exact_parent_family_from_any_population
```

It accepts any actual population P avoiding a word s and any countable family of actual population hosts. It produces an actual population Q that avoids s, has exactly one parent of each label at every nonroot, has its entire word language contained in P's, preserves the original biological roots, and admits no injective map into any listed host with any finite global edge-stretch bound. The hosts need not avoid s or have exact parent counts. Consequently every avoidable word has an exact-parent avoiding class with no single universal member and no countable universal family under the usual graph embeddings. This conclusion does not require a separate nonemptiness hypothesis for that restricted class.

If the supplied P already has exact parent counts, the earlier endpoint `avoiding_no_countable_exact_parent_bounded_stretch_population_family` applies directly, preserving the whole original language instead of just inclusion. More generally, terminal cloning preserves each individual incoming parent count per label through `incomingParentEquiv`; exact uniqueness is only one convenient specialization.

**New formal endpoints and verification.**

The final source is [TerminalCloneAvoiders.lean](C:/Users/Owner/Documents/Alexander-Open-Questions-2026-09-29/embedding/TerminalCloneAvoiders.lean), SHA256 `F074F86ED6A678BA011175EB2D17BE3A2D95D7EE69C2DE2A7E5DDC7D8947A783`.

| Endpoint in `TerminalCloneAvoiders` | Line | Content |
|---|---:|---|
| `terminalClone` | 33 | Actual complete population object |
| `noncanonical_has_no_children` | 62 | Explicit terminal-individual property |
| `terminalClone_language` | 70 | Equality of the entire infinite-word language |
| `incomingParentEquiv` | 81 | Parent-set equivalence separately for each label |
| `terminalClone_preserves_unique_parents` | 98 | Exact-one-parent-per-label preservation |
| `rootsEquiv` | 117 | Equivalence of actual roots for terminal cloning |
| `no_countable_host_family` | 162 | Diagonal against all encodable locally finite relational hosts |
| `no_countable_bounded_stretch_family` | 195 | One population rules out every finite global stretch |
| `avoiding_no_countable_exact_parent_bounded_stretch_population_family` | 218 | Exact-parent avoiding source specialization |
| `selectParents` | 267 | Complete population after choosing one parent per label |
| `selectParents_exact` | 288 | Exact uniqueness for the selected population |
| `selectParents_realizes` | 298 | Language inclusion into the original population |
| `selectParents_root_iff` | 304 | Roothood unchanged pointwise |
| `selectParents_rootsEquiv` | 310 | Actual-root equivalence for selection |
| `selectedClone_rootsEquiv` | 320 | Actual-root equivalence for both operations combined |
| `avoiding_no_countable_exact_parent_family_from_any_population` | 334 | Strongest arbitrary-avoider corollary |

All sixteen selected new endpoints compiled with only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`. The final compile exited 0 with no warnings or errors. A source scan found no `sorry`, `admit`, or declared `axiom`. The check used the already installed Lean 4.33.1 and existing cache with Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`; it did not install anything or rebuild the main repository.

The exact final evidence is [TerminalCloneAvoiders.check.json](C:/Users/Owner/Documents/Alexander-Open-Questions-2026-09-29/embedding/TerminalCloneAvoiders.check.json) and [TerminalCloneAvoiders.compile.log](C:/Users/Owner/Documents/Alexander-Open-Questions-2026-09-29/embedding/TerminalCloneAvoiders.compile.log). [check-lean.ps1](C:/Users/Owner/Documents/Alexander-Open-Questions-2026-09-29/embedding/check-lean.ps1) records the import-path construction and check procedure. The original generic theorem and the new module have 26 selected, freshly checked axiom endpoints in total.

**Boundaries that remain.**

| Category or extra condition | Current result |
|---|---|
| Ordinary weak, induced, directed or label-preserving graph embeddings | Negative for every avoidable word; stronger structures imply the weak injective map already excluded. |
| Every finite global edge-stretch bound, allowed to depend on the map | Negative, with one population defeating all bounds and all countably listed hosts. |
| Exactly one parent per label at each nonroot | Now negative for every avoidable word; parent selection supplies an initial exact-parent avoider. |
| Prescribed exact incoming counts in an already supplied population | Terminal cloning preserves all of them, label by label. |
| Fixed uniform upper bound on the number of children | Unsettled by these constructions. The canonical parent of an expanded fibre can acquire arbitrarily many children. |
| Exact parent counts together with a requirement that every vertex have a child or lie on an infinite future path | Not preserved by terminal cloning. The new individuals are deliberately terminal. |
| Arbitrary unbounded-stretch topological embeddings or ancestry-only embeddings | Not settled. The source paths need not land inside any host ball controlled by a finite global stretch constant. |
| Arbitrary noninjective homomorphisms | Not excluded. Projection onto the original population is itself a label-preserving homomorphism. |
| Uncountable host families or hosts lacking countability/local finiteness | Not addressed by this diagonal. |

The appropriate next research gate is independent review of the new terminal-clone/parent-selection formulation, followed by integration into the owning research repository. All work in this lane is confined to this scratch directory; the prior sources and repository were not edited, and nothing was published, sent to another person, or archived.

