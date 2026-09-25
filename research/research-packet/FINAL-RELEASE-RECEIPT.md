# Published research package: final release receipt

The package is merged in [PR #5](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/pull/5). The owner's local clone is clean on `main` at the merge commit.

## Exact revision and verification

- Tested head: `e0ff308a10702d6f0f43c914f8260525f1ac820c`.
- Merge commit: `425fee8c90e15656caea954ac92beaf28a5d869f`.
- Published tree: `b8a92b409632e9cc0d5320060250e279b137ecfc`, identical to the tested tree.
- [Hosted Linux verification](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/actions/runs/36106341968): all job steps passed, including the core and pinned Mathlib axiom audits, six finite-path tests, local certificate, interval comparison and sharp-trajectory diagnostics.
- Formal coverage: 33 Std core modules; 275 selected core endpoints and 19 real-number endpoints. Both receipts' source hashes match exact committed bytes. Only `propext`, `Classical.choice` and `Quot.sound` are allowed in the endpoint axiom reports.
- Mathematical formatting: 2,167 expressions across 56 Markdown files passed the local MathJax check. Actual GitHub previews were visually checked for table formulas, fractions, subscripts, hyphen-adjacent math, piecewise definitions and aligned equations. GitHub protected inline math and fenced math blocks avoid Markdown processing errors.

## Reading route

1. [Brief mathematical handoff](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/main/HANDOFF-FOR-ALEXANDER.md): results worth reviewing and exact prior-work boundaries.
2. [Formalization coverage](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/main/FORMALIZATION.md): theorem-to-module mapping and hypotheses.
3. [Prior-work audit](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/main/PRIOR-WORK-AUDIT.md) and [search record](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/main/research/PRIOR-WORK-SEARCH-2026-09-24.md): sources, nearest results, meaningful distinctions and retrieval limits.
4. [Ten research proposals](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/main/TEN-RESEARCH-IDEAS.md): checked seeds, open extensions and decisive next tests.
5. [Reproduction guide](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/main/REPRODUCE.md): commands and pinned dependencies.

## What the research review changed

Alexander's prior work already supplies broad inspecies/cofinite-descendant phenomena and overlapping root-cone examples. His older avoiding constructions also have inspecies structure. Those features alone are not presented as new. His 2013 discussion already names forbidden-subtree and rank-theoretic directions.

The narrower results worth expert review include sharp Thue-Morse matching bounds and equality cases; phase and finite-edit extensions; arbitrarily slow finite avoidance; a fixed-gender avoiding inspecies with an arbitrary prescribed aperiodic binary target and a uniform three-child cap; and critical-degree conservation/rigidity statements. The source classification and its construction retain their attribution.

The full matching-height formula remains conjectural. The cap-two problem, general-label rigidity, general finite-alphabet positive formalization and full cellular-automaton dynamics remain open here. The literature map is bounded and does not prove global novelty. No biological or psychological empirical conclusion follows from formal correctness alone.

The final documentation pass made positive-start, after-all-roots and positive-period hypotheses explicit, corrected one paper title, clarified reviewed versus normalized hashes, and updated stale historical scope paragraphs. Lean and audit-source bytes were preserved throughout the formatting pass. No email was sent and no task was archived.
