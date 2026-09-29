# Exact checkpoint and continuation route

**Verified proof commit:** `1ac3dd9446e7264336f0764040ff47ad684099cb`. Local combined PASS: 77 project modules and 415 selected declarations (317 prior, 98 additions); Lean 4.33.1 with the pinned Mathlib revision. Only `propext`, `Classical.choice`, and `Quot.sound` appear. Final audit target recompiled at a clean commit with source/object-validated dependency reuse. [Receipt and scope](verification/RESULT.json).

The complete objective is not being declared finished. The marked Big-ARG
construction and its conditional connection to Alexander now have general
proofs; the paper also contains Little-ARG, asymptotic, algorithmic and empirical
claims that remain separate. All 52 source families are preserved in the
[current ledger](../completion/COVERAGE.md). The final local proof commit,
source hashes, selected-declaration audit, toolchain and raw logs are recorded
in [verification/RESULT.json](verification/RESULT.json). Earlier module
receipts are development evidence, not substitutes for that combined check.

## What this checkpoint establishes

- The marked recorder starts from any finite n>0 and tracks distinct lineage
  IDs, intervals, single-crossover cuts, mergers, event types, fresh vertices
  and consumed/allocated IDs. Validity follows from its actual updates.
- The continuous-cut law chooses an extant lineage or unordered distinct pair
  uniformly, and a breakpoint uniformly in (0,L). The actual evolving
  frontier's conditional mark law is proved, including its adaptedness.
- Raw records have a natural Borel encoding, and the stopped recorder and
  dated-history realization are measurable probability constructions.
- Raw validity is Borel measurable by a proved rational-witness reduction.
  `WongDatedSupport.historyLaw_ae_validDated` states almost-sure validity
  directly under the output law. The independently supplied finite-endpoint
  argument is preserved as a written supporting proof, not relabelled as a
  separate Lean theorem.
- The dated-history projection reads stored frontiers and dates. Its law is
  exactly the existing stopped count-and-time process. Almost every realized
  history is valid, has finitely many events, strictly chronological completed
  edges, and finite physical absorption time. The terminal sequence tail
  contains no further events.
- Raw single-event decoding handles identical parent endpoints. It retains
  the interval boundary and two lineage identities. The inverse is defined
  on the raw encoding range; no arbitrary-file parser is claimed.
- The owner-map bridge has explicit transfer hypotheses for IAP, reflection,
  ancestry convexity, connectivity, specieslike sets and saturated maximality.
  Formal counterexamples rule out inference from sound paths alone.
- The extensions include invariance under finitely many ancestry errors in
  each row and non-recovery of global specieslike status from deterministic
  summaries of a finite gARG over the declared abstract completion class.
  `WongPedigreeRobust.iap_iff_of_finite_projection_errors` additionally permits
  finitely many ancestry disagreements per representative across an onto
  owner map with finite fibres; its weaker hypothesis transfers IAP alone.

The source rates specialize to a=1, b=rho, and the count parameter is theta=2rho.
The stronger real-time semigroup/generator characterization is not inferred
from the path law. Conditioning on the whole count/clock path is used only
for the spatial-mark cylinder, never to claim a fresh exponential clock after
revealing its future value.

## Precisely unproved statements and shortest routes

1. **Discrete source interpretation.** The checked breakpoint law is normalized
   Lebesgue measure. Figure A1 and the Little description use discrete links.
   Define the cut law on {1,...,m-1}, m>=2, and prove the corresponding uniform
   singleton masses. Parameterize the marked construction by a probability
   measure supported on the genome interior, then instantiate both laws.
   Specify the single-site no-recombination case separately. No equivalence
   between the discrete and continuous spatial laws is asserted.

2. **Little ARG and matched sample observations (B01-B03, B06, A01).** The
   unproved target is equality in law of a named sample-ancestry observation
   of Big and Little processes at matched parameters. The Little state and
   kernel are not yet defined. Start with a finite ordered segment partition
   carrying ancestral-sample counts (or explicitly stronger sample sets),
   prove split/overlay/retirement invariants, then construct the kernel.
   Only after that can a coupling or pushforward-law theorem establish the
   target. Big-ARG finite absorption is not a proof of this missing equality.

3. **Expected event growth (B07-B08).** Almost-sure finite absorption alone is
   not a finite-expectation theorem. For total event count J and fixed n>=2,
   first establish finite expectations or a monotone finite-state
   approximation. The intended increment recurrence at the literal rates is
   `(k-1)d_k - 2rho d_(k+1) = (k-1)+2rho`, with E_1[J]=0. The minimal solution,
   uniqueness conditions and asymptotics remain unproved. Only then compare
   the source's O(exp(rho)) wording and rate conventions. The ledger records
   a normalization concern, not a proved erratum.

4. **Statistical cluster identifiability.** The proved obstruction is universal
   exact recovery over abstract ancestry completions. It is not equality of
   DNA sampling distributions under a diploid population model. Choose that
   pedigree class, recombination/mutation law and observation distribution
   explicitly. Then prove the target cluster predicate is constant on its
   distribution fibres, or exhibit two admissible model histories with equal
   distributions and different cluster status. Thatte's positive results and
   Gravel-Steel's genetic-ghost results constrain, but do not decide, this
   new target.

5. **Representation and empirical remainder.** Computable full serialization,
   external tskit conformance, general multiple-crossover events, source
   figures, benchmarks, mutation inference and claimed algorithmic complexity
   retain their individual ledger obligations. No theorem count closes them.

There is no remaining failed theorem in the admitted modules. Earlier
compiler failures are retained in development logs where available; the
exact-commit result governs acceptance. Scope reviews remain separate from
Lean's proof checks. No biological species classification follows from these
ARG or pedigree predicates alone.

## Coordination and recoverability

Work is on the isolated branch `codex/wong-alexander-marked-2026-09-27`, based
on `01db8c4cbb82000950ff7d3e7252b5438416c7c3`. The original checkout was not
edited. The recorder, source-law audit and pedigree bridge had distinct path
owners; shared lake/audit/coverage files were integrated by the coordinating
lane. A single OS lock serialized compiler access with the separate time and
self-reference project. This checkpoint does not claim a new hosted run or
publication. The chat and its history remain visible and unarchived.
