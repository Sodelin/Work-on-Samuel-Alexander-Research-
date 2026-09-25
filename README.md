# Working on Samuel Alexander's research

This repository develops bounded follow-on questions from Samuel A. Alexander's [2013 paper on biologically unavoidable sequences](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v20i1p31) and the [2026 classification manuscript](https://github.com/avg-netizen/biological-unavoidability). It keeps proofs, finite computations, conjectures, and unfinished formalization separate.

**Start here:** [Research map](RESEARCH-MAP.md) explains the research directions in plain language and traces each to its sources. [Brief handoff](HANDOFF-FOR-ALEXANDER.md) gives a compact route for Dr. Alexander or another reviewer. The [status table](STATUS.md) specifies exactly what is proved, computed, or Lean checked.

> **Current mathematical status:** Lean checks the full sharp bound `3L(v) <= 8v-1` for every `v>=1` in the Thue-Morse avoiding population, the equality formula `L(3*2^n-1)=8*2^n-3`, and the fact that these are exactly the equality starts. The proof includes the actual Thue-Morse bits, every dyadic run, and a bridge to the original edge-labelled graph. Lean also checks actual graph counting, infinite subcritical impossibility for natural birth order, the binary avoidance construction, its specieslike-cluster bridge, the exact two common-ancestor cones, the obstruction to whole-graph common ancestry for every binary natural-date population, and the rational algebra behind the corrected static speed-region comparison. All eleven modules build; all 80 selected endpoints pass the axiom audit. [FORMALIZATION.md](FORMALIZATION.md) gives the precise coverage and remaining premises.

## Results and research questions

| Line | Current result | Evidence | Next mathematical step |
|---|---|---|---|
| [Thue-Morse sharp path length](research/thue-morse/NEXT-INVARIANT.md) | `3L(v) <= 8v-1` for all `v>=1`, with equality exactly at `v=3*2^n-1` and `L(v)=8*2^n-3`. | Complete independently reviewed proof and [full Lean theorem](lean/SamuelAlexanderResearch/SharpThueMorse.lean), including actual bits, dyadic trajectories, and original-edge semantics. Existing scans and the [sharp diagnostic](research/thue-morse/sharp_check.py) remain finite corroboration. | External proof and prior-work review; optional formalization of the exact first-hit formula and real-coefficient optimality, which remain prose corollaries. |
| [Degree boundary](notes/DEGREE-BOUNDARY.md) | Required `k` labels and child cap `d<k` preclude an infinite naturally ordered population; binary fixed-gender prefix imbalance is at most its root count. Finite ambient critical conservation is also checked. | [Actual graph proofs](lean/SamuelAlexanderResearch/PopulationCounting.lean), including generated infinite prefixes and [statement review](notes/POPULATION-COUNTING-FORMALIZATION.md). | Two-child fixed-gender avoidance; real-date enumeration bridge; infinite critical conservation. |
| [Specieslike-cluster bridge](notes/SPECIESLIKE-BRIDGE.md) | The whole binary avoiding graph is maximal specieslike, satisfies reflection, and fails common ancestry. With common ancestry imposed, exactly two root cones are maximal. | [Lean graph and avoidance composition](lean/SamuelAlexanderResearch/BinaryPopulation.lean), [two-cone theorem](lean/SamuelAlexanderResearch/SpeciesCones.lean), and [scope note](notes/SPECIES-BRIDGE-FORMALIZATION.md). The full positive theorem remains an explicit premise in Lean. | Extend the formalization to the fixed-gender lift and audit boundary label coverage. |
| [Universal binary root obstruction](lean/SamuelAlexanderResearch/RootObstruction.lean) | Every `BinaryNatPopulation` has the distinct roots `0` and `1`, so its whole graph cannot satisfy common ancestry. | Checked for every population in the binary natural-date model, beyond the particular avoiding construction. | General finite-alphabet root counts and the real-date enumeration bridge. |
| [Periodic lifeline certificate](notes/PERIODIC-LIFELINE.md) | Constant-label paths give a convex-hull-intersection bound; fixed weighted static mixing cannot improve it. | Written dynamical reduction, [finite local-rule checker](checks/check_local_certificate.py), and [Lean rational mixing theorem](lean/SamuelAlexanderResearch/StaticMixing.lean). | State or phase constraints that improve the static intersection, followed by prior-work review. |
| [Automatic-sequence corollary](notes/AUTOMATIC-SEQUENCES.md) | Universality of the specific binary family `P_s` is decidable when `s` is supplied by a finite automaton. | Direct combination of the 2026 manuscript's criterion with the known decidability of ultimate periodicity for automatic sequences. | Implement a certified or independently checked decision procedure if useful. |

The notes identify their precise graph model and quantifiers. A finite search cannot prove an infinite claim; a Lean build checks only the statements encoded in its source. [STATUS.md](STATUS.md) lists the claim by claim verification boundary. The full positive classification, the real-date enumeration bridge, and infinite critical-degree conservation remain explicit gaps. Alexander's [2026 Example 14(1)](https://arxiv.org/html/2602.05274v1#S6) already exhibits the related root-cone phenomenon; no claim of discovering that phenomenon or establishing literature priority is made here.

## Navigate and reproduce

- [RESEARCH-MAP.md](RESEARCH-MAP.md): motivation, dependencies, precise questions, current answers, and possible extensions.
- [HANDOFF-FOR-ALEXANDER.md](HANDOFF-FOR-ALEXANDER.md): short external review guide and three specific questions.
- [STATUS.md](STATUS.md): proof, computation, and Lean status for every line.
- [FORMALIZATION.md](FORMALIZATION.md): exact checked statements, premises, and remaining gaps; [endpoint audit](verification/formal-audit.json) and [statement review](verification/STATEMENT-REVIEW.md).
- [REPRODUCE.md](REPRODUCE.md): local commands and finite-check scope.
- [SOURCES.md](SOURCES.md): primary sources, links, and hashes for the supplied document versions.
- [SEARCH-LOG.md](SEARCH-LOG.md): bounded literature search and its limits.
- [PROVENANCE.md](PROVENANCE.md): attribution and claim language.
- [Local verification receipt](verification/LOCAL-RECEIPT.md): exact checks and saved artifact hashes.
- [GitHub verification workflow](.github/workflows/verify.yml) and [first CI receipt](verification/CI-RECEIPT.md): Lean build and small Python checks on pushes and pull requests.
- [Thue-Morse proof challenge](TASKS/THUE-MORSE-SHARP-BOUND.md) and [degree-boundary Lean challenge](TASKS/DEGREE-BOUNDARY-LEAN.md): bounded briefs for a stronger proof or formalization run.
- [Specieslike-cluster bridge](notes/SPECIESLIKE-BRIDGE.md): direct connection to Alexander's 2026 species paper. An [exploratory interface note](explorations/COMPLEX-SYSTEMS-INTERFACE.md) compares possible dynamical extensions with Levin and Friston; it is outside the core proof program.
- [Outreach draft](OUTREACH-DRAFT.md): an editable note and short video outline that preserve the current proof boundaries. No message has been sent.

The source papers and video transcript are linked and identified, not copied into this public repository. Contributions are welcome when they include exact statements, source citations, a reproducible check where applicable, and a clear separation between checked and conjectural claims.
