# Research map

The user's intended cross-paper connection is **Wong et al. (2024), genome
ancestral recombination graphs, to Alexander's organism/population and
specieslike graph framework**. The two sources describe different mathematical
objects. The [Wong bridge audit](notes/WONG-ALEXANDER-BRIDGE-STATUS.md) records
the exact source pages, checked adapters, missing hypotheses and next proof
contracts. This connection now leads the research program.

The separate [classification manuscript](https://github.com/avg-netizen/biological-unavoidability)
provides an avoiding graph for each non-eventually-periodic binary word.
Alexander's [2013 positive theorem](https://arxiv.org/html/1212.0186v2) supplies
the other side of the classification. Our ten extensions of this construction
have checked answers to their principal questions in the scopes recorded in
[TEN-SOLUTIONS](TEN-SOLUTIONS.md). They do not settle the entire Wong bridge or
all of Alexander's open problems.

~~~mermaid
flowchart TD
  W[Wong finite genome ARGs] --> R[Sample-supported ancestry relations]
  W --> O[Genomes to organism owners]
  R --> Q[Information preserved or lost by observations]
  O --> A[Infinite Alexander population hypotheses]
  A --> S[Specieslike and inspecies predicates]
  A --> B[Binary word classification]
  B --> H[Exact matching heights and digit recurrences]
  B --> D[Degree thresholds and finite port encodings]
  S --> C[Productive cores and boundary repairs]
  W --> F[Finite observations do not determine infinite futures]
  F --> A
~~~

## Current mathematical coverage

| Branch | What is checked in the package | Remaining substantial work |
|---|---|---|
| Wong finite gARG foundation | Finite acyclic interval-annotated records; acyclic local relations; an exact all-node parent representation under unique local parenthood; comparable local ancestors; bounded injective topological numbering with exact ancestry reflection; piecewise-constant ancestry away from breakpoints. | Canonical interval serialization, sample-tracing algorithm, concrete traversal runtime, and stronger input-validation conventions. The all-node parent representation and sample-restricted relation are separate checked objects. |
| Ancestral-material restriction | Exact sample-ending path preservation, idempotence, nested-sample composition and union laws; exact indexed recovery iff every incidence is supported; explicit failure when erasure precedes restriction and an invisible-edge counterexample. | Full simplification algorithms: unary suppression, diamond rewrites and truncation above sample MRCAs are not this restriction operation. |
| Finite history and infinite populations | Two connected, locally finite, finite-root natural-date completions of any ordered finite prefix preserve old edges and ancestry. One is a whole inspecies/maximal specieslike set; the other fails whole-graph IAP. | Compose the finite gARG encoding with these witnesses in one exact endpoint. The completions are mathematical constructions, not inferred biological futures or a diploid-labelled model. |
| Genome/pedigree interface | Fixed-locus paths survive erasure; paths project to owner equality or organism ancestry under explicit compatibility. | Justify an owner map in a concrete biological model, then establish that model's infinite population and cluster hypotheses. |
| Quantitative avoidance | The sharp phase-zero bound and equality set, optimal real coefficient, complete attained maximum at every start including zero, and certified ten-coordinate digit evaluator. | A literal integer-module 2-regularity wrapper is a separate check; optimal representation size and generalizations to other substitutions are not established. |
| Phase and finite edits | Every phase/start has an exact maximum algorithm. Finite edits preserve the optimal coefficient; the universal integer additive allowance and exact equality test are checked. | A joint phase digit recurrence and the best smaller additive allowance for each individual edited target. |
| Quantitative aperiodicity | A break modulus gives an explicit iterated-clock upper bound. Aperiodicity alone allows arbitrarily slow finite avoidance. | Useful moduli and sharp rates for additional concrete word families. |
| Critical degree and port dynamics | General finite-alphabet minimum-width rigidity; actual critical-population finite port encoding; eventually periodic fair schedules realize every infinite word. | Classification beyond minimum width, effective schedule extraction for additional input models, and stronger quantitative bounds. |
| Permanent genders | Cap two is sufficient for prescribed binary aperiodic avoidance while retaining a whole-graph inspecies; smaller caps are impossible. | Optimal root counts and constraints beyond the checked construction. |
| Species interfaces | Exact IAP/inspecies criteria; root-cone and maximality results; productive pruning preserves the infinite word language; finite deficiency exactly characterizes deletion-only repair on a fixed retained set. | General maximal-specieslike existence, arbitrary transformation-preservation criteria, and biological interpretation of a concrete infinite model. |
| Cellular automata | A complete synthetic three-state rule, a state potential that excludes nonzero horizontal finite-support spaceship motion, and a same-rule optimal static bound, including real convex hulls. | Improvements for natural binary rules or published rules, and other directions or certificate classes. |
| Observation and dynamics | Recovery iff fibre constancy and exact deterministic prediction iff observation compatibility. | Specific biological or psychological state spaces, transitions, observations and evidence. These generic facts are not an instantiated scientific theory. |

The three new bridge modules received individual compiler/axiom checks in the
current continuation: AncestralRestriction (11 selected endpoints),
FiniteHistoryCompletion (7) and WongGARG (10). Their registration in a fresh
aggregate receipt and hosted CI is a separate integration check. The current
proof inventory is in [FORMALIZATION](FORMALIZATION.md) and
[STATUS](STATUS.md), with machine-readable source inventories in
[verification](verification). Receipts apply only to the files and toolchain
they identify.

## Why the Wong connection is mathematically useful

Wong's Appendix E uses persistent node identities and unsuppressed local
parent arrays. Sample-based restriction recovers the sample-supported indexed
edge relation; recovering every original edge also requires support for every
retained edge-position incidence. The source audit states this condition and
the checked counterexample without it. The current parent-pointer theorem
represents the whole local relation; it does not claim execution of tskit's
sample-tracing algorithm.

That exact finite representation still does not determine an infinite
genealogical future. An owner map needs a per-edge compatibility proof, and an
infinite population must satisfy its own birth-order, finiteness and role-label
conditions. Specieslike status adds connectedness, IAP and ambient convexity.
The contrasting-completion theorem establishes this limitation for exact
finite ordered topology and ancestry, not merely for incomplete measurements.

Neither Wong's shared ancestors across local trees nor the repository's
Thue–Morse digit identities establish literal graph self-similarity. The new
breakpoint theorem states local constancy between interval boundaries, which
is another distinct property. Any scale-symmetry claim needs an explicit map
and a specified preserved structure.

## Attribution and the four deliverables

The [prior-work audit](PRIOR-WORK-AUDIT.md) and
[older-construction comparison](notes/OLDER-CONSTRUCTIONS-AND-RANK-AUDIT.md)
keep established ideas visible: Alexander already discusses inspecies,
cofinite descendants, multiple-root cones, universal-graph questions and
ordinal-rank directions. Wong already describes the genome/pedigree
relationship and information loss in local-tree simplification.

The former [full-height conjecture](research/thue-morse/FULL-HEIGHT-CONJECTURE.md)
now has a [checked proof](notes/FULL-HEIGHT-PROOF.md) and certified evaluator.
The conjecture file is a historical development artifact; its former status
must not be copied into a current open-problem list.

Use [DELIVERY-MAP](DELIVERY-MAP.md) to separate the reproducible Lean release,
the readable email to Alexander, the focused VibeMathed candidate, and the
public notebook. The email should explain the Wong bridge and its exact
boundary. The VibeMathed candidate is the distinct sharp Thue–Morse
quantitative result answering the separate September manuscript's earlier
question. A source formalization and a newly resolved open problem are
different contribution types.

For detailed review, use the [handoff](HANDOFF-FOR-ALEXANDER.md),
[question ledger](QUESTION-LEDGER.md), and
[reproduction guide](REPRODUCE.md). The
[complex-systems appendix](explorations/COMPLEX-SYSTEMS-INTERFACE.md) remains
exploratory; no concrete Levin, Friston, psychological or consciousness
model is established by the present graph results.

