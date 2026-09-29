# Internal review and remaining external review

Date: 2026-09-25.

## Review of the ancestry theorem

Root reviewed the complete deterministic proof. A separate existing public-writing task and its bounded internal reviewer also checked the statements. No mathematical flaw was found under the five explicit assumptions. This is internal AI-assisted review, not independent external expert endorsement.

Three points from that review are incorporated in the manuscript and claim ledger:

- An infinite IAP set is **contained** in one recurrent component modulo finitely many exceptions. It need not equal the entire component modulo finite; sparse infinite subsets also satisfy the classification.
- Uniform L is mathematically stronger than necessary. It suffices that each organism reaches an entire later same-deme cohort at some individually chosen finite time; local-parent coverage then preserves saturation. The current formal theorem may use uniform L, so this sharpening must remain separately labelled until checked.
- Ordinary independent two-parent Wright–Fisher reproduction does not almost surely satisfy universal local dissemination. For fixed deme size N>=2, a specified organism has probability r=(1−1/N)^(2N)>0 of receiving no parental selections. Choosing one specified organism per generation gives independent no-child events under fresh independent parent draws. The chance all selected organisms avoid childlessness through k generations is (1−r)^k, tending to zero. Thus the all-time structural premise has probability zero in that ordinary model. Our conditional stochastic corollary requires a different reproduction mechanism or a weaker theorem; it cannot be presented as a direct application to Chang's model.

## Review of the culture example

The full two-dimensional stability threshold is m<1/8, distinct from the m<1/6 existence/restricted-mode condition. Formal verification includes local geometric contraction and epsilon convergence, not merely eigenvalue arithmetic.

The final response function is rationalFlow(g,k,d)=g/(1+k*d^2), not the earlier exponential sketch. Its strictly positive floor provides neutral mixing. There is one-way culture-to-exchange coupling, no epigenetic variable and no reciprocal gene-to-culture update.

## Review of the published-model result

A second lane compared the Fogarty affinity recursions, normalizer and marginals with the source on pp. 66–67. The full-range no-polymorphic-fixed-point proof handles both affinity parameters equal to one and permits simplex boundary points as long as both marginals remain interior.

Root derived the additional odds-contraction argument. The source-audit lane independently checked both coefficient identities and the sign conditions before formalization. A separate internal reviewer also compared the final global-fixation statement with the written proof and reported PASS; see rate-statement-review.md. Novelty has not been established by these checks.

## External review still needed

- Does each encoded statement express the intended manuscript claim without a hidden or inconsistent premise?
- Is the IAP/component classification already an immediate named result in genealogy or temporal networks?
- Is the affinity fixation bound already known, including its adaptive-parameter version?
- Are these results interesting enough as a short mathematical note or formalization contribution?
- What weaker survival/mixing assumptions would make the pedigree theorem relevant to finite-population biological models?

No reviewer's identity, approval or acceptance is implied. The package is suitable for asking these questions precisely.
