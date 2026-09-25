# Verification status

## Wong graph mathematics and scope

The new [Wong–Alexander outline](WONG-ALEXANDER-OUTLINE.md) records the composed
interfaces and exact limits. See the endpoint manifests and final source-hash
receipts for the checked inventory.

| Module | Exact contribution | Boundary |
|---|---|---|
| WongGARG | Finite interval DAG, local-parent forest under unique parenthood, derived ordering, exact natural-number path encoding, breakpoint-wise ancestry constancy. | Nonempty annotations and canonical records are explicit additional conditions; interval segmentation is not normalized. |
| AncestralRestriction | Sample-path preservation, idempotence, nested/union laws, exact support criterion and erasure counterexamples. | Removes nonancestral material; does not remove unary nodes or implement tskit. |
| AncestryContraction | Removing unretained intermediate nodes preserves exactly retained-node ancestry, also after sample restriction. | Relation-level semantics; event identities, path lengths and normalized interval output are not preserved or generated. |
| FiniteHistoryCompletion and WongAlexander | Exact embedding of an actual finite gARG into contrasting infinite connected populations, with real dates and opposite whole-species status. | Abstract topology completion, not organism-owner inference, fixed-gender coverage or a prediction of an actual biological future. |
| WongExamples | Two valid finite three-node interval DAGs have identical sample-extracted local relations and different original graphs. | A reconstruction-boundary example, not a claim that every raw ARG loses information. |
| WongLocalArity | Local arity bounds, unary presence distinction and finite backward-walk bounds. | Counts original distinct children; traversal bound is not software runtime measurement. |
| WongEventEncoding | Ordered full-span/single-crossover inheritance becomes an actual interval gARG with matching topology, local routes and paths. Distinct ordered parents identify an interior cutoff. | Does not validate all classical event child arities, normalize storage or establish stochastic inference. |

These are source formalizations and project deductions. Priority and empirical
validity require separate evidence; a passing checker is not a novelty claim.


Updated during the ten-proposal solution pass of 25 September 2026 UTC.
The exact checked files and endpoint counts are in the [core](verification/formal-audit.json)
and [real](verification/real-audit.json) receipts. [FORMALIZATION.md](FORMALIZATION.md)
states the actual models and hypotheses.

| Claim | Status | Remaining boundary |
|---|---|---|
| Positive eventual-periodic unavoidability | Lean proof for binary populations; arbitrary real-birthdate transport and binary classification iff. | The general finite-alphabet positive theorem is not encoded. Attribution remains Alexander's. |
| Negative binary construction | Lean proof against actual source edges; unconditional specieslike and cap-two fixed-gender classifications. | No claim to have originated the source construction. |
| Arbitrary birth-order presentation | Enumeration and general degree/root adapter checked; real specialization uses Mathlib reals. | Quantitative slopes still measure the particular graph's vertex index, not arbitrary timestamps. |
| Infinite critical conservation | Actual full-degree counts, triangular crossing bound, finite total defects, eventual regularity and constant width. | Critical cap and simple-edge assumptions are explicit. |
| Minimum crossing rigidity | For every finite $`k`$, triangular minimum width on every tail cut forces exactly the directed $`k`$th power of a ray. | Classification above minimum width remains separate. |
| Fixed-gender threshold | Cap two suffices for every prescribed aperiodic target, even with whole-graph inspecies/reflection; lower caps are impossible. | The new line-graph witness has three roots; optimal root count is not claimed. |
| Productive pruning and boundary repair | Whole core eligibility, exact infinite language preservation, cluster distinctions, and optimal deletion-only repair are checked. | Repair optimality fixes the retained vertex set. |
| Finite ports | Actual arbitrary-population encoder, exact schedule decoder, fairness, crossing-slot correspondence and periodic all-word universality are checked. | Schedule periodicity is an explicit additional hypothesis, not a consequence of finite width. |
| General IAP/inspecies and root-cone criteria | Lean endpoints; exact specializations and consecutive-layer universality. | Does not solve unrestricted maximal-species existence or identify empirical species. |
| Sharp phase-zero Thue-Morse theorem | Full Lean bound, attained maximum, equality family and exact equality indices. | Global novelty not established. |
| Auxiliary first-hit formula and real coefficient | Exact first-hit endpoint and no-smaller-real-coefficient theorem checked. | No separate Filter.limsup endpoint is claimed. |
| Finite-edit stability | Real coefficient $`8/3`$ optimal; exact frontier decomposition and equality test; $`8m-1`$ is the best universal integer additive constant. | The best smaller constant for a particular edited target remains separate. |
| Shifted target and graph | Checked $`5a`$ sharp bound, real coefficient optimality, attained maxima and full equality iff at $`v=3\cdot2^n-a-1`$, $`a\le2^n`$. | General two-variable digit recurrences are open. |
| Arbitrarily slow finite maxima | For every function $`f`$, an aperiodic target has attained maxima exceeding $`f`$ at increasing starts; every other start also has a finite maximum. | Executability is relative to $`f`$; no formal computability-theory interface. |
| Complete height formula | Universal closed form and ten-coordinate binary recurrence proved for actual attained maxima at every start. | The earlier capped finite experiments are retained only as discovery history. |
| Quantitative modulus | A period/antiperiod break modulus gives an explicit iterated-clock bound on matching lengths. | Modulus existence uses classical choice; a computational bound requires supplying a modulus. |
| Indexed ancestry and observations | Erasure, projection, information-loss and exact recovery/prediction criteria checked. | No empirical genetic/species inference follows automatically. |
| Stateful cellular automaton | A complete three-state rule has exact static east support one, but no finite-support horizontally moving spaceship. Both rational and literal real convex-hull statements are checked. | This is a synthetic rule and a specified static certificate class, not an improvement for Life-like or published rules. |
| Automatic-target decision corollary | Written combination of cited results. | No decision implementation or Lean proof. |

The [independent statement review](verification/GAP-CLOSURE-REVIEW.md) addresses
model fidelity separately from the axiom audit. The latter builds dependencies
before checking selected endpoints and allows only `propext`, `Classical.choice`
and `Quot.sound`. A successful finite experiment is never promoted to a
universal theorem by this ledger.

The [current workflow](.github/workflows/verify.yml) runs the core build/audit,
six finite-path tests, local certificate check, interval/trajectory diagnostics,
and pinned real-project audit. Older local and CI receipts remain historical
records. Their success does not certify a later patch.
