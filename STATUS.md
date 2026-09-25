# Verification status

Updated during the coordinated gap-closure pass of 25 September 2026 UTC.
The exact checked files and endpoint counts are in the [core](verification/formal-audit.json)
and [real](verification/real-audit.json) receipts. [FORMALIZATION.md](FORMALIZATION.md)
states the actual models and hypotheses.

| Claim | Status | Remaining boundary |
|---|---|---|
| Positive eventual-periodic unavoidability | Lean proof for binary populations; arbitrary real-birthdate transport and binary classification iff. | The general finite-alphabet positive theorem is not encoded. Attribution remains Alexander's. |
| Negative binary construction | Lean proof against actual source edges; unconditional specieslike and cap-three fixed-gender classifications. | No claim to have originated the source construction. |
| Arbitrary birth-order presentation | Enumeration and general degree/root adapter checked; real specialization uses Mathlib reals. | Quantitative slopes still measure the particular graph's vertex index, not arbitrary timestamps. |
| Infinite critical conservation | Actual full-degree counts, triangular crossing bound, finite total defects, eventual regularity and constant width. | Critical cap and simple-edge assumptions are explicit. |
| Minimum crossing rigidity | Binary width three on a whole tail forces $+1,+2$; fixed genders then imply all-word realization. | General-$k$ theorem and cap-two avoidance remain open. |
| Three-child productive core | Permanent genders, arbitrary prescribed aperiodic target, two roots, inspecies/specieslike/reflection and avoidance checked. | Whether two children suffice remains open. |
| General IAP/inspecies and root-cone criteria | Lean endpoints; exact specializations and consecutive-layer universality. | Does not solve unrestricted maximal-species existence or identify empirical species. |
| Sharp phase-zero Thue-Morse theorem | Full Lean bound, attained maximum, equality family and exact equality indices. | Global novelty not established. |
| Auxiliary first-hit formula and real coefficient | Exact first-hit endpoint and no-smaller-real-coefficient theorem checked. | No separate Filter.limsup endpoint is claimed. |
| Finite-edit stability | Actual length-preserving transport, attained maxima, upper bound and lower witnesses; real coefficient $\frac{8}{3}$ optimal. | The exported start displacement is at most the edit-prefix length $m$. Optimal additive constants remain open. |
| Shifted target and graph | Checked $5a$ sharp bound, real coefficient optimality, attained maxima and full equality iff at $v=3\cdot2^n-a-1$, $a\le2^n$. | General two-variable digit recurrences are open. |
| Arbitrarily slow finite maxima | For every function $f$, an aperiodic target has attained maxima exceeding $f$ at increasing starts; every other start also has a finite maximum. | Executability is relative to $f$; no formal computability-theory interface. |
| Complete height formula | Concrete closed-form/ten-coordinate conjecture passes stored and fresh exact finite checks. | No universal proof or Lean theorem. Capped cases are explicitly skipped. |
| Indexed ancestry and observations | Erasure, projection, information-loss and exact recovery/prediction criteria checked. | No empirical genetic/species inference follows automatically. |
| Static speed-region comparison | Rational strict example and actual real convex-hull inclusion checked. | CA lifeline existence, limiting velocity, and a stronger rule-specific speed theorem remain unformalized. |
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
