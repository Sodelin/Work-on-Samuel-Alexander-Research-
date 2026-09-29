# VibeMathed submission draft: quantitative Thue–Morse matching heights

Status: prepared, not submitted. The browser submission requires sign-in; browser automation was interrupted by a Windows sandbox initialization failure. The field text below is ready for review and manual entry at [VibeMathed](https://vibemathed.com/submit).

## Result name

Sharp quantitative bounds for Thue–Morse matching paths in an avoiding population

## Problem as previously posed

Section 5 of the separate manuscript *A classification of biologically unavoidable sequences*, dated 10 September 2026, asks for useful explicit bounds on matching-prefix lengths from a fixed starting vertex for the Thue–Morse target. Use the [pinned original question](https://github.com/avg-netizen/biological-unavoidability/blob/3d6175e3e23f67bd68e7be591b5a9a6d04e496a3/paper.md#5-universality-and-computability-in-the-witness-family).

This is a follow-up question in that AI-assisted manuscript. It is not an identified quantitative question posed by Alexander in 2013, nor a claim to originate the earlier classification solution.

## What was proved

Let $`L(v)`$ be the greatest number of edges in a path starting at $`v`$ in the specified Thue–Morse avoiding population whose labels match the unshifted Thue–Morse target. For every $`v\ge1`$,

```math
3L(v)\le8v-1.
```

Equality holds exactly at $`v=3\cdot2^n-1`$ for $`n\in\mathbb N`$, with $`L(v)=8\cdot2^n-3`$. The coefficient $`8/3`$ cannot be lowered even after allowing a fixed additive constant. The proof includes attainment and the connection to the original edge relation.

The current follow-up branch additionally proves a full formula for every natural starting vertex, including $`L(0)=1`$, and a certified ten-coordinate integer evaluator. Its release status is tracked separately from the already published sharp theorem.

## Checkable source

- [Published sharp theorem source](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/425fee8c90e15656caea954ac92beaf28a5d869f/lean/SamuelAlexanderResearch/SharpThueMorse.lean).
- [Published proof and interpretation](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/425fee8c90e15656caea954ac92beaf28a5d869f/research/thue-morse/NEXT-INVARIANT.md).
- [Successful hosted verification of the released tree](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/actions/runs/36106341968).
- [Current full-height proof](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/codex/research-followup-2026-09-25/notes/FULL-HEIGHT-PROOF.md).

Use the first, immutable URL as the primary result source until the follow-up release has completed its own hosted verification.

## Suggested form metadata

| Field | Value |
| --- | --- |
| Short name | Thue–Morse matching-path bounds |
| Result | Proved |
| Solve date | 2026-09-25 |
| Source name | GitHub repository with Lean proofs and reproducible verification |
| Model/vendor | OpenAI Codex, GPT-6 family; OpenAI |
| Field/detail | Combinatorics; infinite labelled graphs and automatic sequences |
| Publication | Announced; public proof repository, not journal peer reviewed |
| Status | Candidate, review pending; curator may determine the final category |
| Verification | Conservatively describe as Lean checked with internal statement audits; request the curator's assessment of the site's independent-anchoring requirement |
| Year posed | 2026 |
| Posed by | Separate AI-assisted classification manuscript, Section 5, pinned above; no named human author in its front matter |

## AI contribution disclosure

The user directed the research questions and requested explanations, literature checks and formal verification. Codex agents developed the mathematical arguments, exploration tools, Lean proofs and exposition, with other agents checking source attribution, theorem statements and counterexamples. These are internal project audits; no independent human expert endorsement is claimed.

## Verification note and limits

The sharp theorem is in the released tree at commit `425fee8c90e15656caea954ac92beaf28a5d869f`. That tree passed hosted Lean 4.33.1 builds, the 275-endpoint core and 19-endpoint pinned-Mathlib audits, and the recorded computational checks. The logical axiom allowlist is `propext`, `Classical.choice`, and `Quot.sound`. New follow-up work has separate local receipts for 370 core and 30 Mathlib endpoints; those local receipts must not be presented as hosted CI for the later branch.

The result concerns one explicitly defined population and target phase. It does not solve Alexander's remaining general species-existence, universal-avoider or ordinal-characterization questions. The bounded literature search found the explicit prior quantitative question and no inspected earlier source with the same sharp statement; worldwide priority is not certified. A source question being AI-assisted is disclosed rather than used as a claim about its mathematical importance. Acceptance and verification labels are decisions for VibeMathed's reviewers.
