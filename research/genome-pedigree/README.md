# Missing diploid ownership and whole-population IAP

Status: **candidate research contribution with explicit prior-art limits**.
This packet studies a deterministic observation map. It is independent of the
completed Royal Society formalization checkpoint and of the parallel sampled-
parent recovery control. Start with the [one-page explanation](../../GENOMES-AND-PEDIGREES.md).

## The result

**Theorem.** Fix the entire realized, unpaired genome-copy transmission graph
whose vertices are `(t,i)`, with natural generation `t` and lane `i` in
`{0,...,7}`. Its only edges are `(t,i) → (t+1,i)`, all carrying the interval
`[0,1)`. For every natural `N`, there are two diploid ownership assignments
agreeing through generation `N`, with these properties:

1. Each organism owns exactly two contemporaneous genome copies. Both
   pedigrees have four organisms per generation and exactly four founders.
2. A pedigree edge exists **if and only if** an actual genome transmission
   witnesses it. Every nonfounder has two distinct parents; every organism
   has exactly two children. Both pedigrees are weakly connected.
3. The first whole population satisfies Alexander's IAP and is a maximal
   specieslike cluster. The second whole population fails IAP and is not
   specieslike. The same pair also differs on whole-population inspecies.
4. The organism graphs have real generation birthdates, finite birthdate
   sublevels and finite child sets, with infinitely many organisms.

The genome-copy identities, dates, edge intervals, and all realized
transmissions coincide. Ownership after the observed prefix is omitted from
the common observation. Even a consistent binary organism-sex label on every
copy can coincide in the two histories, with opposite-sex parents for every
nonfounder.

The quantifier permits any finite **length** of agreement, using the specified
mixing history on that prefix. It does not assert that every possible observed
ownership prefix admits these two continuations.

Consequently no rule taking this complete unpaired transmission graph plus a
bounded prefix of ownership can correctly decide whole-population IAP on the
constructed family. This quantifies over all deterministic rules, including
noncomputable ones. It does not quantify over probability laws or assert a
statistical error lower bound.

## Definitions and proof

Organism `(t,j)` is encoded as `4*t+j`, for `j` in `{0,1,2,3}`. Genome copy
`(t,i)` is encoded as `8*t+i`. At each generation, ownership is one of three
partitions, with columns indexed by organism `j`:

| Partition | 0 | 1 | 2 | 3 |
|---|---|---|---|---|
| M0 | {0,1} | {2,3} | {4,5} | {6,7} |
| M1 | {1,2} | {3,4} | {5,6} | {7,0} |
| M2 | {1,2} | {3,0} | {5,6} | {7,4} |

The first schedule alternates M0 at even generations with M1 at odd
generations. Choose the even switch generation `S = 2*(N+1)`. The second
schedule agrees through S, then alternates M0 at even generations with M2 at
odd generations. Adjacent blocks are parent and child exactly when they
intersect: their shared lane supplies the genomic edge. No unwitnessed
pedigree edge is inserted.

Each allowed adjacent pair of partitions gives two distinct incoming and two
distinct outgoing edges at every organism. Give even-index organism blocks
one sex and odd-index blocks the other; the two incoming parents always have
opposite parity. M1 and M2 assign each individual lane the same owner-sex
parity. This is a segregation-compatible, nonselfing autosomal construction;
it permits consanguineous mating and no recombination on the displayed
interval. A full meiosis, recombination or sex-chromosome probability model
has not been supplied.

For the first schedule, let A and B be the Boolean adjacency matrices for
M0→M1 and M1→M0. Direct finite calculation gives `ABA = BAB = J4`, the all-ones
matrix. Every organism therefore reaches all organisms exactly three
generations later. Diagonal transitions extend these paths to every later
generation. Thus only finitely many organisms are non-descendants of any
fixed organism. Whole IAP follows from the existing definition. Any two
vertices have a later common descendant, proving weak connectivity; whole-
graph convexity is automatic. Whole is consequently maximal specieslike.
The existing whole-inspecies/cofinite-descendants equivalence gives the
inspecies conclusion. The local calculation also shows only three of four
organisms are reached in two generations, so the uniform bound three is
tight; that tightness observation is written mathematics, not a separately
exported Lean endpoint.

After S in the second schedule, both transition matrices are
`diag(J2,J2)`. Their idempotence preserves the two lane groups `{0,1,2,3}` and
`{4,5,6,7}`. Any organism in the first tail group has descendants at arbitrarily
late generations there and no descendants in the other group. It has
infinitely many descendants and infinitely many non-descendants, contradicting
IAP. The initial M0/M1 transition forms an eight-cycle joining all four
founders. Every later organism connects to its same-index founder through
diagonal parent edges, so the **whole** pedigree remains weakly connected.

All graph edges advance exactly one generation. Four vertices per generation
give finite sublevels even for arbitrary real date bounds. There are four
founders and infinitely many generations. These establish the source's
biosphere assumptions, not biological plausibility of an infinite future.

Agreement of the ownership schedules through S implies agreement through N.
If an exact IAP decoder on the stated observation existed, it would return
the same answer for these two inputs, contradicting their opposite IAP
values. This completes an all-generation proof rather than extrapolation
from finite simulation.

## The exact source-model maps

The finite Lean constructor uses natural-number coordinates and `[0,1)`, so
the covered locus is exactly 0. This implements one unrecombined abstract
region. There are no nucleotide strings, sequence likelihoods or claims
about every possible interval system. "Complete" means every vertex and
realized transmission in the declared model is retained.

| Interface | Proved preservation | Limit |
|---|---|---|
| Wong finite gARG | `PairingGARG.finiteARG T` has exactly generations 0 through T, eight copies each, full interval `[0,1)`, and all eight final copies sampled. Its topology is exactly next-generation, same-lane transmission. Annotations are nonempty, local parents unique, and every edge sample-supported. | The infinite history itself is not a finite gARG. No Big ARG, Little ARG, coalescent or sampling law is instantiated. |
| Finite gARG to the common infinite copy graph | `PairingBridge.code` is injective and `finite_topology_iff_genome` preserves and reflects edges. `finite_pedigree_exact_image` proves the exact owner-image pedigree on each truncation. Sample extraction at the covered locus retains every edge. | The supplied ownership map is extra data, not inferred by this construction. |
| Organism graph to Alexander | Theorems use the existing `SpeciesBridge.IAP`, `Specieslike`, `MaximalSpecieslike` and `SpeciesGlobalIAP.Inspecies`. `generation_dated_biosphere` supplies real generation dates to `WongAlexander.RealDatedBiosphere`. | These are idealized genealogical predicates, not an identification of empirical species. |
| Royal Society time-and-memory track | The earlier [source-faithful reading route](../../TIME-AND-MEMORY.md) and checked reduction results remain intact. | No Royal Society theorem is asserted to solve this biological problem; no full author question is closed. |

The preservation obstruction has a two-edge witness:

```text
organism {0,1} at generation 0
    → organism {1,2} at generation 1     (genome lane 1)
    → organism {2,3} at generation 2     (genome lane 2).
```

Every edge is an exact image of a transmission. But every genomic path stays
on one lane, while the endpoint organisms have disjoint lane sets. No genomic
path connects any representative of the first organism to any representative
of the last. Thus exact image **edges** do not supply the ancestry-reflection
premise of the existing owner-transfer theorem. This is why applying that
theorem here would be invalid.

## What is established, new, and still conjectural

**Established background, reused here:** genetic and genealogical ancestry
differ; pedigree reconstruction may be non-identifiable; diploid pairing is
extra structure; exact quotient edges need not lift compatible paths. The
existing repository IAP, finiteness, inspecies and gARG definitions are reused.

**Candidate new deduction/application:** the complete conjunction in the
theorem above, particularly identical complete realized copy histories,
exactly witnessed pedigree edges, diploid and degree constraints, arbitrary
finite owner-prefix agreement, and opposite whole-population IAP. The
[eight-source prior-work review](PAIRING-PRIOR-ART.md) found no exact matching
result or direct stronger equivalent. This is not proof of worldwide priority.

Thatte's [diploid-pedigree representation](https://arxiv.org/pdf/1008.0153v3)
includes both **potential** parental homologues, allowing a pairing rule that
does not apply to our realized-transmission chains. Kirkpatrick's
[likelihood non-identifiability results](https://arxiv.org/pdf/1602.08183)
quantify over all observed data under declared stochastic models. A single
common realized history is not that stronger statistical statement. Neither
comparison may be omitted when presenting this result externally.

**Unproved extensions:** whether the obstruction survives a specified
stochastic law with a useful positive-probability or almost-sure statement;
which biologically motivated restrictions on ownership remove it; and which
finite observations identify the relevant ownership under such restrictions.
No likelihood has been fitted. No new experimental dataset or biological
mechanism is established.

For the displayed pair, an ownership query at the first switched odd
generation separates them: lane 0 shares an organism with lane 7 in M1 and
with lane 3 in M2. Physical or recorded co-assignment of those copies would be
extra information. This is a mathematical separating query, not a validated
experimental protocol. It is not a universal finite query for IAP: the switch
can always be placed later than a prescribed finite observation prefix.

The practical value is a precise data-contract check: if organism ancestry is
the target, retain individual associations or prove a replacement path-lifting
condition. The theorem does not show that richer genomic evidence, an
individual table, or stochastic inference is futile.

## Verification

The three new Lean modules are [PairingCore.lean](PairingCore.lean),
[PairingGARG.lean](PairingGARG.lean) and [PairingBridge.lean](PairingBridge.lean).
The main endpoints are:

| Declaration | Claim |
|---|---|
| `PairingCore.constrained_counterexample` | Arbitrary finite prefix; connectivity, degree constraints, opposite IAP, specieslike and inspecies status |
| `PairingCore.owner_exactly_two` | Exactly two copies in every owner fibre |
| `PairingCore.edge_exact_image` | No extra or missing organism edges relative to actual transmissions |
| `PairingCore.no_iap_decoder` | No exact rule on the specified common graph plus bounded owner observations |
| `PairingCore.exact_edges_do_not_lift_paths` | Explicit failure of ancestry-path reflection |
| `PairingCore.parents_opposite_sex`, `same_copy_sex` | Consistent biparental sex control without distinguishing the data |
| `PairingBridge.finite_pedigree_exact_image` | Exact finite Wong-to-pedigree edge mapping |
| `PairingBridge.generation_dated_biosphere` | Real generation dates and all four biosphere conditions |

Use installed Lean 4.33.1 and Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`, with the external dependencies already
available in the chosen `real/.lake/packages` directory:

```text
python research/genome-pedigree/verify.py --dependency-root real
python research/genome-pedigree/check_packet.py
python checks/check_math_format.py GENOMES-AND-PEDIGREES.md research/genome-pedigree
```

The replay compiles every project dependency from this checkout into a fresh
private folder, then audits every public theorem in the three new modules.
Only external pinned package outputs are reused. The
[proof receipt](verification/PROOF-RECEIPT.json) records source and log hashes,
compiler exit codes and axiom reports. The allowed foundational axioms are
`propext`, `Classical.choice` and `Quot.sound`; placeholder axioms are rejected.
Development reuse is labelled in the receipt and rejected by the release
integrity check. The separate
[CI workflow](../../.github/workflows/genome-pedigree.yml) performs fresh replay.

The [independent falsification review](PAIRING-FALSIFICATION.md) supplies a
second mathematical check and distinguishes written claims from compiler
evidence. Its early status statements are a review of the proposed
construction; the replay receipt is the authority for the final Lean status.

## Checkpoint and stopping criterion

This lane is complete when the theorem, exact interfaces, bounded prior-work
assessment, clean fresh replay and newcomer reading route are preserved.
Increasing coverage of unrelated known results is not part of this gate.
The exact stochastic and ownership-restriction questions above remain open.
The next public claim should stay at the level of this constrained
counterexample until a broader theorem and novelty review support it.

This packet is suitable for mathematical review as a candidate research
note. It is not a claim of empirical discovery, a journal submission, or an
outreach message. The completed formalization track remains valuable and
separate; this discovery track uses proof to test a specific proposed result.
