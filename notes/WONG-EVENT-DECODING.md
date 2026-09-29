# Wong event conversion: normalized inverse and classical event arity

## Result and attribution

**This is an attributed formalization of the first, unsimplified event-to-genome conversion in Wong et al. (2024), not a new open-problem solution or a full-paper certificate.**

Primary source: Yan Wong, Anastasia Ignatieva, Jere Koskela, Gregor Gorjanc, Anthony W. Wohns and Jerome Kelleher, *A general and efficient representation of ancestral recombination graphs*, GENETICS 228(1), iyae100 (2024). [DOI](https://doi.org/10.1093/genetics/iyae100); [publisher's PDF in the University of Edinburgh repository](https://www.pure.ed.ac.uk/ws/portalfiles/portal/458588307/iyae100.pdf).

Source locators (PDF has a cover sheet, so zero-based PDF page index equals printed journal page):

- Printed pp. 2–3, **Event ARGs**, Fig. 2: common-ancestor and crossover events, ordered left/right parent convention.
- Printed pp. 3–4, **Ancestral material and sample resolution**, Fig. 3: topology duplication and full/split interval annotation; the p. 4 paragraph states the first-step information correspondence.
- Printed p. 4, **A diversity of structures**: classical binary events versus more general gARG node degrees.
- Printed p. 2, **Genome ARGs**: dates and application-specific metadata are additional attributes.

The new lemmas make the restricted correspondence precise. They also expose why it does not provide a general reconstruction theorem after information-removing transformations.

## Input assumptions

[WongEventDecoding.lean](../real/WongEventDecoding.lean) imports the existing `WongEventEncoding` module. Its common coordinate span is nonempty: $`l<h`$. Coordinates have a linear order; no density assumption is needed. Each parent specification is one of:

1. Root, with no parent.
2. A single parent, supplying $`[l,h)`$.
3. Two **distinct ordered parents**, supplying $`[l,q)`$ and $`[q,h)`$, with $`l<q<h`$.

The third condition is explicit in `Normalized`. Cut interiority is already carried by `ParentSpec.crossover`. The proofs use the left endpoint and one or both cut positions; hence they apply to discrete as well as continuous coordinate orders whenever an interior cut exists.

## Exact new conclusions

| Endpoint | Checked conclusion |
|---|---|
| `equal_parent_crossover_same_local` | If both parents have the same node identity, a crossover has the local inheritance of a single-parent event. This shows the semantic normalization boundary. |
| `crossover_left_identified` | Complete local inheritance determines the left parent identity. |
| `crossover_right_identified` | Complete local inheritance determines the right parent identity. |
| `normalized_same_local_iff` | For normalized specifications, equality of full local inheritance is equivalent to equality of the entire specification: constructor, ordered parents and cutoff. |
| `same_local_of_records_eq` | Identical raw first-step interval records imply identical local inheritance. |
| `normalized_records_injective` | The raw record encoder is injective on the explicitly normalized domain. |
| `encode_decode` | Encoding the classical inverse of an in-range record set returns that record set. |
| `decode_encode` | The classical inverse of an encoded normalized specification returns the original specification. |
| `Graph.parents_identified` | Equal raw encoded graph records identify every normalized node's parent specification. |
| `Graph.graph_identified` | With fixed node IDs and span, the complete normalized input graph is identified by its raw encoding. |
| `Graph.encoded_canonical` | Normalized graphs satisfy the existing gARG `CanonicalRecords` condition: at most one record for each parent-child pair. |
| `kind_signature_injective` | The four stated strict classical degree signatures distinguish the event kinds. |
| `decode_kind_signature` | The explicit degree classifier returns each event kind on its signature. |
| `encoded_degrees` | Event encoding preserves both parent and child counts. |
| `encoded_kind_recovered` | The classical adapter's event kind is recovered from the encoded topology. |
| `classical_kind_unique` | Two classical adapters on the same graph have identical event-kind maps. |
| `classical_encoded_sample_iff` | In the adapter's constructed gARG, the sample flags agree with the sample event kinds. |

`normalizedEncodingEquiv` packages the two inverse identities into an equivalence between normalized specifications and the encoder's range. It is a definition assembled from the checked identities, not a separate empirical claim.

### Why the full specification is identifiable

The left endpoint reveals the first parent. A coordinate at the larger of two candidate cuts reveals the second parent. Distinct parents ensure a switch is observable. The pre-existing cutoff-identification lemma then forces equal cuts. Root and single-parent cases are distinguished by whether any parent is present and whether that parent changes. This completes identification beyond the earlier lemma, which held both ordered parent identities fixed in advance.

## What “decoding” means here

`EncodedRecords` includes a proof that the records lie in the normalized encoder's range. `decode` uses `Classical.choose` to select a preimage. The proved injectivity makes that preimage unique.

**This inverse is noncomputable.** It is neither a file parser nor an executable validator for arbitrary input. It does not parse tskit tables or certify their serialization. The proof says an exact normalized first-step encoding loses none of the parent specification; it does not supply an efficient algorithm for discovering that specification from external data.

The equal-parent counterexample concerns *local inheritance semantics*. Two adjacent raw records may retain a split even when their local relation agrees with a full-span single record. It is therefore incorrect to use that counterexample to claim that all raw record encodings themselves are noninjective.

## Strict classical adapter

`ClassicalShape` adds explicit binary degree conventions to the otherwise broader `EventGraph`:

| Kind | Number of parents | Number of children |
|---|---:|---:|
| Sample | 1 | 0 |
| Internal common ancestor | 1 | 2 |
| Recombination | 2 | 1 |
| Terminating root common ancestor | 0 | 2 |

This is a **restricted interface chosen to represent the usual binary convention**. It excludes the degenerate one-node sample/root case, unary pass-through nodes, multifurcations and simultaneous multiple crossovers. It does not assert that every event history or every gARG has these signatures. An extra root/sample constructor would be required to include the isolated-sample case. The adapter designates its samples using the sample kind, with the correspondence checked in `classical_encoded_sample_iff`.

Graph directions remain ancestor-to-descendant. Parent/child degree names use biological ancestry orientation, even when a rootward traversal follows those edges backwards.

## Explicit exclusions

- Arbitrary sample-resolved or simplified gARGs are outside the inverse's domain unless separately shown to be exact first-step encodings.
- Removing sample-unsupported ancestry, contracting unary nodes or merging intervals may remove event-history information; none of those operations are reversed here.
- The generic `EventGraph` does not contain event times, mutation histories, a stochastic law or application metadata. These are not reconstructed.
- The strict adapter recovers kind labels because its degree convention distinguishes them. The generic parent specification alone does not distinguish every historical meaning of a single-parent node.
- Fixed node identities are preserved. This is not graph isomorphism up to relabeling.
- `CanonicalRecords` is the existing one-record-per-parent-child definition; it does not certify general maximal interval merging or byte-level serialization canonicality.
- No claim about DNA-based ARG inference, biological species, likelihoods, coalescent event rates, asymptotic performance or novelty is established.

## Integrated verification

The source is registered in the real-number project and in `RealAudit.lean`.
The fresh local aggregate audit passed 209 selected endpoints on 25 September
2026, including the six new modules (58 endpoints). Read the exact source
hashes and axiom reports in [the receipt](../verification/real-audit.json).
Only `propext`, `Classical.choice` and `Quot.sound` were used. Hosted verification
is tracked on [PR #6](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/pull/6/checks).

Reproduce from the repository root with `python checks/audit_lean.py --real`
after preparing the pinned Mathlib project as described in [REPRODUCE](../REPRODUCE.md).
This source formalization does not certify the tskit implementation.
