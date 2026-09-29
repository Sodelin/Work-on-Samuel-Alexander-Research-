# Exact sampled-family recovery: source-question audit

29 September 2026. Bounded review of the existing `sampled-family-recovery` submission, its actual Lean statements, Kim–Mossel–Ramnarayan–Turner (KMRT), and Mossel–Vulakh. No proof changes or new compilation.

**Best supported contribution:** an exact finite-sample benchmark for recovery from observed symbols, paired with a precisely constructed dependence example. It identifies how much this particular family estimator gains from independent blocks and demonstrates why correct single-block marginals alone do not justify that gain. This is useful model calibration with a complete formal probability calculation. Its status as a previously open mathematical result has not been established.

## What was proved

The model fixes finitely many nonempty sampled families of sizes `m_i`. Each family has a disjoint parental pair; every parent's symbol is distinct from every other parent's symbol at each block. Each child copies a parent fairly and independently across children, blocks and families. Observations are exact.

Join two sampled children if they agree at any corresponding observed block, and return the connected components. For every `B >= 1`, exact recovery of the whole sampled-family partition has probability

```math
\prod_i\left[1-(2^{m_i-1}-1)2^{-B(m_i-1)}\right].
```

The counting argument is elementary but complete: different families never acquire sharing edges, and a family disconnects exactly when its inheritance vectors consist of one complementary pair with both vectors represented. A bijection counts every exceptional configuration. A separate observation theorem proves that the computed relation uses symbol equality; the hidden family labels occur only in the target correctness condition. The exact probability is then transported to the actual observed-array distribution.

For three siblings and two blocks the success probability is `13/16`. The project's earlier restricted rule requiring all three to agree at some block gives `7/16`. This is a comparison of these two specific procedures. In the repeated-block law, draw one independent fair bit per child and reuse that bit at every block. Every individual block still has the complete correct joint law across children, but this family's graph-recovery probability remains `1/4` for every positive block count. This counterexample concerns the sharing-component procedure; no impossibility result for every conceivable estimator is proved here.

## The actual published open question

KMRT's [Section 1.6, Question 1, PDF p. 6](https://arxiv.org/pdf/2005.03810v1#page=6) asks about low fertility, finite alphabets, and dependence between inheritance blocks. Its dependence clause is: “Can we analyze more generic models of inheritance where blocks are not inherited i.i.d. from parents?” The main paper already proves multigeneration asymptotic reconstruction in Theorem 6.1, p. 33, under its specified generative model. Section 2.3, pp. 10–11, explains complications with pairwise replacements for its recursive procedure.

The relation between those questions and this packet is exact but limited:

| Direction in Question 1 | What the packet supplies | What remains unresolved |
|---|---|---|
| Fertility near the population-replacement threshold | Arbitrary fixed nonempty sampled family sizes in one generation. | A multigeneration random-pedigree guarantee with fertility near two. There is no fertility parameter or growing-depth analysis in this theorem. |
| Finite symbol alphabet | The observed-output endpoint admits a finite alphabet and requires per-block parent-symbol injectivity. | The finite-alphabet problem with possible symbol collisions. A finite type in Lean does not remove the strong distinct-symbol hypothesis; it must be large enough for all parents in this fixed population. |
| Non-independent inheritance blocks | A concrete law preserving every one-block joint marginal while eliminating this estimator's extra-block gain. | Recovery guarantees for a broader dependent inheritance class, and information-theoretic limits across all estimators. The positive product formula still assumes independence. |

These are a positive control and a boundary example relevant to Question 1, not a demonstrated closure of any complete clause of that question. The exact finite question was formulated within this project. The original [claim ledger](../../pedigree-block/LEDGER.json) and [accepted checkpoint](../../pedigree-block/CHECKPOINT.md) expressly make no novelty claim. A new source link cannot supply the missing novelty evidence.

## Closest follow-up and the estimator comparison

Mossel and Vulakh's [2022 preprint v2](https://arxiv.org/pdf/2204.04573v2), published in the [PSB 2023 proceedings](https://doi.org/10.1142/9789811270611_0013), already uses pairwise screening before testing triples: Section 3.2, PDF p. 3, selects candidate pairs using a shared-block threshold. Sections 5–8 study finite simulation performance, inbreeding and modified ancestral-symbol reconstruction, including belief propagation. The paper's simulations do not certify this packet's formula, and this packet supplies no theorem that improves that multigeneration algorithm. Its `13/16` versus `7/16` comparison must therefore keep the exact restricted comparator visible. No simulation or code from the follow-up was rerun in this audit.

## Formal statement and checking boundaries

| Completed claim | Actual source endpoint |
|---|---|
| Disconnection equals the complementary-pair event; adding blocks preserves connectivity | [PedigreeBlockGraph.lean](../../../real/PedigreeBlockGraph.lean), `not_connected_iff_bad`, `connected_of_restrict` |
| Explicit exceptional-event bijection and exact probability; independent coordinates and families | [PedigreeBlockProbability.lean](../../../real/PedigreeBlockProbability.lean), `badEquiv`, `bad_probability`, `config_bit_cylinder`, `families_good_probability` |
| Observed paths preserve families and actual partition recovery equals family connectivity | [PedigreeBlockObservation.lean](../../../real/PedigreeBlockObservation.lean), `observed_path_preserves_family`, `recovered_iff_connected` |
| Exact product formula, including under the observed-array law | [PedigreeBlockRecovery.lean](../../../real/PedigreeBlockRecovery.lean), `recovered_probability`, `output_recovery_probability` |
| Actual repeated-block measure with unchanged one-block joint laws and one-family success | [PedigreeBlockDependence.lean](../../../real/PedigreeBlockDependence.lean), `repeatedLaw_block_marginal`, `repeatedLaw_connected_probability` |

The output-law theorem requires a finite measurable symbol alphabet with measurable singletons and per-block injectivity. The hidden-variable recovery theorem allows an arbitrary symbol type. The repeated-block endpoint is for one family's connectivity; an additional multi-family observed-output repeated-law theorem is not present. The estimator is a mathematical reachability relation, with no certified executable refinement or complexity bound in the packet.

The saved-evidence verifier passed on this audit date: seven modules, 31 selected declarations, 49 artifact hashes, exact proof commit `ae0beee8d04e32c45f28d2f465b924d6816c82a5`. It verified source/log integrity and selected axiom reports; it did not rerun Lean. Allowed axioms are `propext`, `Classical.choice` and `Quot.sound`. The [receipt](../../pedigree-block/verification/RESULT.json) and [internal statement review](../../pedigree-block/STATEMENT-REVIEW.md) preserve the evidence. The earlier 415-declaration ARG audit is separate.

The written distribution-identifiability argument, union-bound consequence, observation-error coupling bound and parent-couple incidence construction remain outside the listed Lean endpoints. No independent-block coupling from Wong's continuous ARG model, infinite Alexander-cluster transfer, or biological species conclusion is supplied.

## Recommended update

Present the exact observed-data probability and dependence construction first. Add the source-question map above as a substantive clarification to the existing submission. Describe this as a project-formulated finite benchmark and dependence boundary for editorial assessment. Do not promote it to “KMRT Question 1 solved,” first use of pairwise inheritance comparisons, a general finite-alphabet reconstruction theorem, or an improvement to REC-GEN. Catalog eligibility and worldwide priority remain unestablished; all completed mathematical evidence remains publicly useful.

The [proposed five fields](VIBEMATHED-FIELDS.json) keep the original contribution visible while fixing the source-question and comparator boundaries. The [evidence ledger](EVIDENCE-LEDGER.json) records the two-paper reading scope and the fresh integrity result.
