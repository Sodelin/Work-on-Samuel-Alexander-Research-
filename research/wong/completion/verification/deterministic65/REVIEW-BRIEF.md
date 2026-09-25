# Wong deterministic integration: statement-first adversarial brief

This brief is for the shared reviewer assigned by the Astra auditor. Read this
file and `selected-statements.txt` before opening proof bodies. Record an
independent attempted counterexample or missing hypothesis before inspecting
the proposed proof. The review is bounded to the three modules and their
source correspondence. Do not compile, edit implementation files, or start
another worker.

Baseline: public commit `138dd529643ae5706a9df6a750bd6344ab967a8a`, with 209
selected real-development endpoints. Proposed addition: MRCA truncation 24,
interval canonicalization 31, simplification normal form 10. The proposed
aggregate is 274 endpoints, including other research in the existing real
development. This number is not a percentage of Wong's paper.

The attributed source is Wong et al. (2024), *A general and efficient
representation of ancestral recombination graphs*, DOI
[10.1093/genetics/iyae100](https://doi.org/10.1093/genetics/iyae100).
The primary XML is `source/PMC11373519-fullText.xml`, SHA-256
`2b77c349f39d2885b3e36d3bcab639a7ef3b9c6217263031aa4bc8f1c2a0d05e`.
Relevant locators: main-text section `iyae100-s3` and Figure 3; Appendix B
`app2`, paragraph 4; Appendix E `app5`, paragraphs 2–3; Appendix G `app7`,
paragraphs 6–7. This is formalization and representation infrastructure for
known source operations; no new biological result is proposed.

## Contracts to challenge

Take a finite acyclic interval gARG G, with fixed node IDs, sample set S,
linearly ordered coordinates, proper half-open intervals, and local edge
relation R(x,p,c) directed ancestor to descendant. Let A be reflexive local
ancestry and Common(x,c) mean that c is an ancestor of every member of S.

1. MRCA truncation keeps an edge exactly when it is sample-supported and its
   child is not Common. A unique latest common ancestor exists when S is
   nonempty, local parents are unique, and some common ancestor exists.
   The finite output preserves sample-to-sample and MRCA-to-sample paths,
   keeps sample IDs, inherits local parent uniqueness and adds no breakpoints.
   Empty and singleton samples and a forest without a common ancestor have
   separate stated behavior.
2. Interval canonicalization merges exactly touching pieces for each ordered
   parent-child pair. Proper sorted nonoverlapping input becomes strictly
   separated. Union membership is unchanged; no endpoint is invented.
   Any two proper strictly separated interval lists with equal membership
   at every coordinate are equal, even over a nondense linear order.
   The actual graph adapter preserves the full AtLocus relation, emits one
   nonempty record per active pair and is idempotent as a storage operation.
3. The combined normal-form theorem returns an actual finite interval gARG
   whose edges are exactly contraction of the truncated sample ancestry,
   retaining samples and locally branching nodes. Under local parent
   uniqueness, every incident nonsample node has at least two children.
   Sample paths and local-MRCA paths survive. Intervals are maximal per pair,
   and canonicalizing this final graph's interval storage changes nothing.

## Boundary challenges and false controls

- Challenge MRCA existence without nonempty samples, with distinct sampled
  local roots, or without unique parents. No unconditional existence claim
  is admissible.
- A supported edge into a common ancestor must be removed. The false claim
  that truncation equals ordinary support extraction must be rejected.
- A sample that is an ancestor may remain unary. Unused catalogue IDs remain
  isolated. The false claim that every catalogue node has at least two
  children after simplification must be rejected.
- Overlapping or unsorted interval lists are outside the separation theorem's
  ordering premise. Genuine gaps must remain; touching pieces must merge.
  Empty annotation records can disappear while catalogue IDs and samples
  remain. Graph topology alone is therefore not always preserved.
- Reconstruction from sample-traced local arrays equals all input local
  edges only under `SampleSupported`; using full `AtLocus` as input is a
  distinct observation. The false unconditional sample-array inverse must
  be rejected.
- Classical cell/record enumeration remains noncomputable. Only the list
  merge is executable here. Reject claims of an executable full exporter,
  an efficient tskit implementation, or byte serialization.
- Storage idempotence is not whole-pipeline idempotence. The combined theorem
  does not identify every Figure 5 intermediate stage or reconstruct literal
  Figure 3/5 data. Reject stronger source-coverage claims.
- These modules do not prove stochastic sample-set/count invariants,
  absorption, holding-time nonexplosion, spatial coupling, or expected cost.

## Deliverable and stopping condition

Return a short review file with (a) attempted counterexamples, (b) exact
theorem names and hypotheses that defeat them or a minimal failing witness,
(c) source wording that the formal statement narrows, and (d) PASS WITH
SCOPED LIMITS or a concrete blocker. Distinguish review from an independent
kernel run. Stop after these three contracts and the listed false controls.
Write only the assigned review artifact; send findings to the auditor and
Wong lead task `01a0d92b-4cf1-7360-84aa-66858089d5ba`.
