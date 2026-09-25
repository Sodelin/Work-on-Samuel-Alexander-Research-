# Completion map: what is finished and what remains

## Wong completion and feedback follow-up — 25 September 2026

The [Wong completion ledger](research/wong/completion/README.md) now maps 52
claim families and records six new integrated modules (58 selected endpoints;
209 in the real aggregate). The [feedback/speciation package](research/feedback-speciation/README.md)
adds a conditional IAP classification, cultural/genetic boundary examples and
a quantitative fixation bound for the published Fogarty affinity model.
Its five new modules contribute 53 selected standalone endpoints; the repository
CI now checks 113 standalone endpoints in 17 files.

The Wong paper remains partly formalized. The feedback theorem has strong
pedigree assumptions, its probability adapter is still written-only, and none
of these additions proves that DNA determines biological species or establishes
novelty. See the exact scopes and [publication verification boundary](research/feedback-speciation/PUBLIC-INTEGRATION.md).
Hosted status is recorded per commit in [PR #6](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/pull/6/checks).

The previous consolidated author email and VibeMathed curator update were both
delivered on 25 September. The original VibeMathed submission remains under
review. This new research batch has not yet been sent as another outreach update.

Updated 25 September 2026. Start here for the current project status. Earlier proof receipts remain valid records of their own snapshots.

## Latest focused follow-up

The [DNA-identification evidence map](research/open-questions/genomic-identifiability/next/README.md) adds known primary literature and a checked finite-evidence extension: overlapping finite-sample support, an obstruction to uniform certainty, robust recovery, and the sharp half-gap boundary in the three-taxon model. This adds eight selected standalone endpoints; it does not prove biological species delimitation. The author has received one consolidated completion email update. The VibeMathed curator follow-up was delivered and verified on 25 September; the original submission is unchanged.

## Where we have reached

**The three main proof directions now have complete, locally checked results at explicit scopes:** ordinal certificates, a universal-embedding obstruction, and maximal specieslike clusters with a real founding window. The earlier quantitative sequence results and finite-genome ancestry results are also complete for their stated models.

This note records local completion before publication. The exact-commit hosted result is recorded in [PR #6 and its checks](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/pull/6/checks). The successful hosted run for the earlier `beca7b8` snapshot certifies that earlier snapshot.

This is meaningful mathematical progress. It gives us precise theorems to share and discuss. It does not yet establish a general biological species detector, a theory of psychology, or independent agreement that each result is new.

## What the results mean

| Direction | What is now locally proved | What the result does not yet establish |
|---|---|---|
| **Ordinal characterization** | For arbitrary vertex and label types, avoiding a target is equivalent to a decreasing ordinal rank on reachable vertex/phase states. Under finite branching, a least natural rank exists and its values are attained. The actual matching-history root rank and first-limit pruning stages are also checked for every `BinaryNatPopulation`. | The explicit history calculation is still binary and naturally indexed. The written Schmidt-rank/kernel calculation and the pruning fixed point for realizing populations remain unformalized. The rank gives no algorithm for arbitrary inputs or hierarchy separating avoiders. |
| **Universal avoiding populations** | A finite-fibre construction preserves the exact infinite-word language and actual population axioms, including real birthdates, at arbitrary vertex and label types. One population defeats every member of a countable host family under injective edge embeddings, and under any finite global edge-stretch bound. | Arbitrarily unbounded stretch, ancestry-only maps, and a prescribed uniform child cap require different results. The graph-growth obstruction is classical; the precise population application needs an exact literature comparison. |
| **Specieslike existence** | Every organism belongs to a maximal connected, convex, reflecting IAP cluster whose founders occur within one fixed nonnegative real duration. The proof constructs its own seed and preserves actual real birthdates, including ties. | The formal organisms have natural-number identifiers. Maximality is within the fixed-window class. No unique partition, species classification algorithm, or empirical biological validity follows. |
| **Genomic identification** | A finite ancestry graph does not fix the whole-specieslike status of every allowed infinite completion. A separate known three-taxon law identifies a tree relationship from its exact probabilities. | These do not identify species boundaries from raw DNA. A biological claim needs a specified target, observation model, and justified history assumptions. |

### Why your priors should change

We should have **more confidence in the exact mathematical implications**: several steps that previously existed only in prose now have complete proof chains. The founder theorem no longer assumes a seed, and the ordinal-certificate theorem no longer requires a binary alphabet or natural-number vertex encoding.

We should keep **originality separate from correctness**. Some results formalize established mathematics. Some apply classical methods to Alexander's populations. Some quantitative statements are candidates for original contributions. A large proof inventory does not tell us which category a result belongs to; source comparison and knowledgeable readers do.

We should keep **biological meaning separate from graph properties**. Alexander's specieslike conditions are a mathematical proposal. The existence theorem proves that the proposed class contains maximal members under the stated constraint. Whether those members track biological species is a further modelling and empirical question.

## What remains, in order

1. **Record the release gate.** The publication owner publishes this frozen packet and records the normal combined verification at its exact commit in PR #6. This note records the completed local proofs; the PR is the current hosted-status record.
2. **Record expert and literature assessment.** Compare the exact theorem statements with prior work and distinguish a useful formalization from a new theorem. The reviewed email is already sent; the VibeMathed entry was submitted and observed under review. The existing monitor covers meaningful responses.
3. **Treat further mathematics as explicit follow-up work.** Schmidt rank/kernel, the realizing-population pruning fixed point, and a generic version of the explicit history-root calculation remain written results. A richer rank hierarchy, unrestricted embedding notions, biological calibration, and psychology models are additional questions with their own completion criteria.

This provides a finite stopping point for the present packet. We can finish the claimed theorem chains and their publication without silently taking on every possible extension.

## Technical verification inventory

The integrated library remains at **405 core endpoints** and now has **151 real/Mathlib endpoints**, including the full founder theorem. The separate research-artifact audit **passed locally with 52 printed endpoints across 11 files** in the previous completion packet. The new eight-endpoint finite-evidence module brings the current selected audit to **60 endpoints in 12 files**; see its [combined local receipt](verification/genomic-finite-evidence-audit-local.json). These counts describe selected checked statements and must not be presented as counts of discoveries or historical open problems solved. The combined local pass was recorded at 10:56:58 UTC on 25 September 2026. The exact-commit hosted result is recorded separately in PR #6 and its checks.

The actual history rank/pruning work has eleven new endpoints plus its six-endpoint prerequisite. The generic natural-certificate and ordinal-certificate files have eight and three respectively. The complete founder proof contributes fifty new registered real endpoints. Historical receipts retain their original counts and source hashes.

## Corrections included in this pass

- The probability example now distinguishes each alternative's probability from their combined probability; the Lean law was already correct.
- The individual finite-edit optimum is recorded as proved.
- Stale wording that no outreach was sent is replaced by the sent/submitted state.
- Published standalone research proofs receive an explicit audit separate from the integrated library totals.

## Navigation

- [Open-question theorem map and evidence](research/open-questions/README.md)
- [Readable genomic explanation](research/open-questions/genomic-identifiability/README.md)
- [Complete real founder-window theorem](notes/REAL-FOUNDER-WINDOW-THEOREM.md)
- [Question provenance ledger](QUESTION-LEDGER.md)
- [Publication snapshots and delivery](PUBLICATION-STATUS.md)
- [Refinement ledger](REFINEMENT-LEDGER.md)
