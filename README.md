# Working on Samuel Alexander's research

A public, AI-assisted mathematics notebook connecting infinite genealogical
graphs, word avoidance, specieslike clusters and cellular automata. Source
results, new deductions, conjectures and finite experiments are identified
separately. This repository has not contacted Dr. Alexander on the owner's behalf.

**Start with the [ten research proposals](TEN-RESEARCH-IDEAS.md),
[brief mathematical handoff](HANDOFF-FOR-ALEXANDER.md), and
[formalization coverage](FORMALIZATION.md).** The proposals now include several
proved quantitative and structural results, alongside precise open questions.

## Current results

| Direction | Result | What remains |
|---|---|---|
| Sharp Thue-Morse avoidance | For $v\ge1$, $3L(v)\le8v-1$; equality exactly at $v=3\cdot2^n-1$, with $L=8\cdot2^n-3$; full first-hit corollaries and real-coefficient optimality. | The candidate closed form for every $L(v)$ is unproved. |
| Stability and phase | Finite edits preserve the optimal coefficient $\frac{8}{3}$; rebuilding the graph from phase $a$ gives $3L_a(v)\le8v+5a-1$ for $v\ge1$ and the same optimal coefficient, with a complete shifted equality classification. | Finer finite-edit equality sets and joint digit recurrences. |
| Slow avoidance | For every growth function, an aperiodic target has attained finite matching maxima exceeding that function along increasing starts. | Useful upper bounds from quantitative aperiodicity data. |
| Fixed vertex genders | Every prescribed aperiodic binary target has a cap-three avoiding productive core that is an inspecies. The retained-subtype classification is checked. | Whether cap two suffices. |
| Critical degree | Full conservation, triangular minimum crossing count, finite total defects and eventual regularity. Binary minimum width forces $+1,+2$ geometry and, with fixed genders, universality. | General-$k$ rigidity and larger-width structure. |
| Formal model closure | The positive binary theorem, birth-order enumeration, actual real-birthdate binary classification, and general degree/root transport are encoded. | General finite-alphabet positive formalization and full CA dynamics. |
| Species and observation | General IAP/inspecies/root-cone criteria, exact avoiding-graph cones, and indexed ancestry/observation-recovery interfaces. | Broad cluster-core and finite-boundary repair theorems. |

The [core audit](verification/formal-audit.json) and [real-number audit](verification/real-audit.json)
record exact endpoints, source hashes and permitted proof dependencies. The
default library is Std-only; the real-number project has a pinned Mathlib
dependency. The [status table](STATUS.md) states the mathematical boundaries.

## Sources and navigation

- [Question ledger](QUESTION-LEDGER.md): where each question originated and what has been answered.
- [Research map](RESEARCH-MAP.md): motivation and relationships between directions.
- [Ten proposals](TEN-RESEARCH-IDEAS.md): precise targets, proved seeds and next decisive tests.
- [Prior-work audit](PRIOR-WORK-AUDIT.md) and [additional source checks](notes/ADDITIONAL-SOURCE-CHECKS.md): verified precedents and remaining priority uncertainty.
- [Biological model scope](BIOLOGICAL-MODEL-SCOPE.md): organism genealogy, fixed genders and genetic inheritance are distinct models.
- [Sharp proof](research/thue-morse/NEXT-INVARIANT.md), [full-height conjecture](research/thue-morse/FULL-HEIGHT-CONJECTURE.md), and [formalization notes](FORMALIZATION.md): reviewable mathematics.
- [Reproduction](REPRODUCE.md), [statement review](verification/GAP-CLOSURE-REVIEW.md), and [verification receipt](verification/FORMALIZATION-RECEIPT.md): exact evidence.
- [Sources](SOURCES.md), [provenance](PROVENANCE.md) and [editable outreach draft](OUTREACH-DRAFT.md): attribution and an optional owner-controlled review route.

Alexander's [2013 positive theorem](https://arxiv.org/html/1212.0186v2), his
[inspecies results](https://arxiv.org/html/1201.2869), and his
[2026 cluster examples](https://arxiv.org/html/2602.05274v1) remain attributed
prior work. The separate [classification manuscript](https://github.com/avg-netizen/biological-unavoidability)
supplies the target-dependent avoiding graph. The quantitative and structural
extensions here require external mathematical and priority review; formal
verification is evidence for the encoded statements, not a novelty certificate.
