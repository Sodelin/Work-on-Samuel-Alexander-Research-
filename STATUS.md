# Verification status

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
