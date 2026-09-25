# Working on Samuel Alexander's research

A public, AI-assisted mathematics notebook connecting infinite genealogical
graphs, word avoidance, specieslike clusters and cellular automata. Source
results, new deductions, conjectures and finite experiments are identified
separately. Publication and outreach status are recorded with the relevant release.

## Latest research progress

**Updated 25 September 2026.** Read the [human-readable progress report](RESEARCH-PROGRESS.md) for the latest results, evidence and remaining work.

| Where to go | What you will find |
|---|---|
| [Research progress](RESEARCH-PROGRESS.md) | What changed, why it is useful, and what is still local or unfinished |
| [Current research PR #6](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/pull/6) | Newer published work awaiting integration with the main branch |
| [Research architecture](RESEARCH-ARCHITECTURE.md) | Three research leads, shared workers, adversarial review and publication rules |
| [Latest verified research checkpoint](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/actions/runs/36173386580) | Research commit `a2644182`: 405 core, 317 real and 234 standalone selected Lean declarations |

**Start with the [ten research proposals](TEN-RESEARCH-IDEAS.md),
[brief mathematical handoff](HANDOFF-FOR-ALEXANDER.md), and
[formalization coverage](FORMALIZATION.md).** The proposals now include several
proved quantitative and structural results, alongside precise open questions.

## Current results

| Direction | Result | What remains |
|---|---|---|
| Sharp Thue-Morse avoidance | The sharp bound, equality cases, [complete all-start height formula](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/a2644182b147eb40816abb278e00c3c6d4709eb8/notes/FULL-HEIGHT-PROOF.md) and [ten-coordinate integer digit recurrence](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/a2644182b147eb40816abb278e00c3c6d4709eb8/notes/DIGIT-RECURRENCE.md) are proved for actual matching paths. | Broader target families and phase-dependent digit recurrences remain separate. |
| Stability and phase | Finite edits preserve the optimal coefficient $`\frac{8}{3}`$; rebuilding the graph from phase $`a`$ gives $`3L_a(v)\le8v+5a-1`$ for $`v\ge1`$ and the same optimal coefficient, with a complete shifted equality classification. | Finer finite-edit equality sets and phase-dependent digit recurrences. |
| Slow avoidance | For every growth function, an aperiodic target has attained finite matching maxima exceeding that function along increasing starts. | Useful upper bounds from quantitative aperiodicity data. |
| Fixed vertex genders | A [cap-two population](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/a2644182b147eb40816abb278e00c3c6d4709eb8/notes/CAP-TWO-SPECIES.md) with permanent genders avoids every prescribed non-eventually-periodic binary target while retaining whole-graph inspecies/reflection properties; the separate cap bound is optimal. | Extensions to other label classes and model assumptions remain separate. |
| Critical degree | Full conservation and [general finite-label rigidity](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/a2644182b147eb40816abb278e00c3c6d4709eb8/notes/GENERAL-RIGIDITY-THEOREM.md): eventual minimum crossing width forces exactly the next-# Working on Samuel Alexander's research

A public, AI-assisted mathematics notebook connecting infinite genealogical
graphs, word avoidance, specieslike clusters and cellular automata. Source
results, new deductions, conjectures and finite experiments are identified
separately. Publication and outreach status are recorded with the relevant release.

## Latest research progress

**Updated 25 September 2026.** Read the [human-readable progress report](RESEARCH-PROGRESS.md) for the latest results, evidence and remaining work.

| Where to go | What you will find |
|---|---|
| [Research progress](RESEARCH-PROGRESS.md) | What changed, why it is useful, and what is still local or unfinished |
| [Current research PR #6](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/pull/6) | Newer published work awaiting integration with the main branch |
| [Research architecture](RESEARCH-ARCHITECTURE.md) | Three research leads, shared workers, adversarial review and publication rules |
| [Latest verified research checkpoint](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/actions/runs/36173386580) | Research commit `a2644182`: 405 core, 317 real and 234 standalone selected Lean declarations |

**Start with the [ten research proposals](TEN-RESEARCH-IDEAS.md),
[brief mathematical handoff](HANDOFF-FOR-ALEXANDER.md), and
[formalization coverage](FORMALIZATION.md).** The proposals now include several
proved quantitative and structural results, alongside precise open questions.

## Current results

| Direction | Result | What remains |
|---|---|---|
| Sharp Thue-Morse avoidance | The sharp bound, equality cases, [complete all-start height formula](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/a2644182b147eb40816abb278e00c3c6d4709eb8/notes/FULL-HEIGHT-PROOF.md) and [ten-coordinate integer digit recurrence](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/a2644182b147eb40816abb278e00c3c6d4709eb8/notes/DIGIT-RECURRENCE.md) are proved for actual matching paths. | Broader target families and phase-dependent digit recurrences remain separate. |
| Stability and phase | Finite edits preserve the optimal coefficient $`\frac{8}{3}`$; rebuilding the graph from phase $`a`$ gives $`3L_a(v)\le8v+5a-1`$ for $`v\ge1`$ and the same optimal coefficient, with a complete shifted equality classification. | Finer finite-edit equality sets and phase-dependent digit recurrences. |
| Slow avoidance | For every growth function, an aperiodic target has attained finite matching maxima exceeding that function along increasing starts. | Useful upper bounds from quantitative aperiodicity data. |
| Fixed vertex genders | A [cap-two population](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/a2644182b147eb40816abb278e00c3c6d4709eb8/notes/CAP-TWO-SPECIES.md) with permanent genders avoids every prescribed non-eventually-periodic binary target while retaining whole-graph inspecies/reflection properties; the separate cap bound is optimal. | Extensions to other label classes and model assumptions remain separate. |
k`$ tail adjacency. Binary fixed-gender universality has its separate hypotheses. | Larger-width structure; one isolated minimum cut does not establish the tail theorem. |
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
- [Sharp proof](research/thue-morse/NEXT-INVARIANT.md), [proved full-height formula](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/a2644182b147eb40816abb278e00c3c6d4709eb8/notes/FULL-HEIGHT-PROOF.md), and [formalization notes](FORMALIZATION.md): reviewable mathematics.
- [Reproduction](REPRODUCE.md), [statement review](verification/GAP-CLOSURE-REVIEW.md), and [verification receipt](verification/FORMALIZATION-RECEIPT.md): exact evidence.
- [Sources](SOURCES.md), [provenance](PROVENANCE.md) and [editable outreach draft](OUTREACH-DRAFT.md): attribution and an optional owner-controlled review route.

Alexander's [2013 positive theorem](https://arxiv.org/html/1212.0186v2), his
[inspecies results](https://arxiv.org/html/1201.2869), and his
[2026 cluster examples](https://arxiv.org/html/2602.05274v1) remain attributed
prior work. The separate [classification manuscript](https://github.com/avg-netizen/biological-unavoidability)
supplies the target-dependent avoiding graph. The quantitative and structural
extensions here require external mathematical and priority review; formal
verification is evidence for the encoded statements, not a novelty certificate.
