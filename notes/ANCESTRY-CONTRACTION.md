# Eliminating unretained ancestry nodes

The module [AncestryContraction.lean](../lean/SamuelAlexanderResearch/AncestryContraction.lean) proves exact ancestry preservation when unretained vertices are eliminated from a directed relation. It is the next formal stage after the separate [ancestral-material restriction](ANCESTRAL-RESTRICTION.md).

The distinction matters for the Wong gARG connection. Ancestral-material restriction discards irrelevant inherited material at each genomic location. Node elimination then compresses paths through vertices that the chosen representation does not retain. These are separate operations with separate hypotheses and conclusions.

## Exact operation

Let R be a parent-to-child relation and K the predicate saying which vertices are kept. HiddenPath R K a b is a nonempty original path from a to b whose internal vertices are all outside K. The contracted relation contains an edge from a to b exactly when a and b are both retained and such a hidden-interior path exists.

This definition can eliminate arbitrary unretained nodes. It does not require them to be unary. As a result, the checked guarantee concerns ancestry between kept nodes, not preservation of branch degree, event identity, path length, or a particular implementation's output graph.

The proof splits every original path at each retained intermediate vertex. The resulting segments are exactly the new contracted edges. Conversely, expanding those edges yields an original path.

## Checked core endpoints

The root task compiled the standalone core module successfully. Its five printed endpoints used only permitted standard axioms or no axioms. This check is separate from the final aggregate repository audit.

| Endpoint | Exact conclusion |
| --- | --- |
| retained_path_iff | Between two retained vertices, contracted reachability holds exactly when original reachability holds. |
| contract_acyclic | An acyclic original relation has an acyclic contracted relation. |
| nested_contraction_paths | Keeping a larger set and then a smaller subset has the same retained-node reachability as contracting directly to the smaller set. |
| locus_retained_path_iff | The same exact ancestry preservation holds separately at every fixed genomic location, with the retained set allowed to depend on that location. |
| resolved_contracted_sample_path_iff | Ancestral-material restriction followed by contraction preserves exactly all paths from a retained vertex to a retained designated sample. |

The nested theorem intentionally compares ancestry relations. It does not assert equality of an arbitrary serialized edge list or of algorithms that apply additional simplification conventions.

## Application to the actual finite interval gARG

The wrapper WongAlexander.extracted_contracted_sample_path_iff in [WongAlexander.lean](../real/WongAlexander.lean) composes the generic result with the actual finite gARG model:

- Start with G.AtLocus x, the original interval-edge relation at location x.
- Apply G.ExtractedAt x, which retains only sample-ancestral material at that same location.
- Eliminate vertices outside K.
- For retained a and retained sample s, the resulting relation has a path from a to s exactly when G.AtLocus x did.

The sample condition is actual membership in G.samples. The identification of G.ExtractedAt with the generic restriction is proved in the same wrapper module, so no equivalence between disconnected definitions is assumed.

The actual wrapper was checked successfully by the root task as one of the eight printed WongAlexander endpoints, with only permitted standard axioms or no axioms. The checked WongAlexander source SHA-256 is 1EC04C06714F359D791CDE0B4892443404F887C486BB59E35F4F24A35C1CB666. This standalone check is separate from the final aggregate repository audit.

## What remains outside this result

Wong et al.'s [2024 paper](https://doi.org/10.1093/genetics/iyae100), especially Appendix G, discusses a family of simplifications. The present result isolates a relation-level ancestry guarantee; it is not a complete verification of tskit's simplify implementation or all of its conventions.

The contracted relation is defined at each locus. Constructing normalized finite interval records for all resulting edges, proving an efficient extraction algorithm, specifying which biological nodes must be kept, and implementing truncation above local MRCAs are further tasks. The pointwise theorem alone does not construct those records or settle those choices.

Genomic location labels remain essential. A path assembled by switching locations can create spurious locus-specific ancestry, as shown by the separate erasure counterexample. Nothing here proves graph self-similarity or turns a finite gARG into an infinite organism population.