# Independent review of the gap-closure pass

This review follows the [first integration review](STATEMENT-REVIEW.md).
Each proof module had one writer; independent agents reviewed statements and
supporting arguments without rewriting the author's module. The core and real
axiom audits separately compile the final sources and record exact hashes.
These are local AI-assisted reviews, not external human refereeing or a
literature-priority verdict.

| Material | Independent review and material scope checks |
|---|---|
| PositiveUnavoidability and BirthOrder | Counting reviewer checked finite child selection, arbitrary finite backward words, periodic blocks, prefix prepending, and the all-Nat classification. Enumeration is genuinely constructed from finite sublevels, with injectivity, surjectivity and tie handling. |
| InfiniteConservation and MinimalCrossing | Thue-Morse reviewer checked full infinite-graph degrees, inclusion of every child in the ambient finite count, triangular crossings, and critical defects. Width three is assumed at every tail cut. Permanent source genders are additional data. Width four is a crossing obstruction, not a child-cap obstruction. |
| FiniteEditStability and PhaseShift | Thue-Morse reviewer checked finite offset invariants, short/zero prefixes, start-zero handling, graph translation/subtraction, and lower witnesses. Finite-edit start displacement is at most `m`; only the suffix cutoff is `min(m,ell)`. Phase bounds rebuild both graph and target. |
| FixedGenderLift | Counting reviewer checked retained-set roots/children, the explicit three-child cover, retained parent coverage, induced ancestry, exact roots, avoidance projection, and the separate non-inspecies cap-four cleaned lift. |
| SlowAvoidance, QuantitativeAvoidance, SharpCorollaries and LayeredUnavoidability | Counting reviewer checked stage coherence, long zero-block aperiodicity, actual prefix witnesses, baseline first-hit minimality, exceptional starts, and all consecutive-layer hypotheses. |
| FiniteAvoidance | Coordinator checked conversion of function prefixes to inductive finite paths, actual finite children, contradiction from unbounded endpoints, endpoint-to-length bound, finite attained maximum, and composition with the increasing slow starts. No finite bound or compactness conclusion is supplied as a premise. |
| FixedGenderReindex | Counting reviewer checked the retained subtype, source labels, root equivalence by surjectivity, filtered child covers with the same numeric cap, both directions of actual path transport, and cap-three classification. |
| PopulationReindex | Counting reviewer checked all arbitrary-presentation hypotheses, exact Option-label preservation, derived finite root/child support, numeric degree from possibly duplicated cover lists, original-vertex roothood and injective `Fin k` root family. |
| RealBridges | Source/plan auditor and a separate coefficient reviewer checked the actual real model, derived enumeration, classification witness, all coefficient casts and inequalities, negative real coefficients and arbitrary additive constants, real root/degree wrappers, and static convex geometry. The [durable detailed report](REAL-BRIDGES-STATEMENT-REVIEW.md) records the final source hash. |
| PhaseExtremal | Counting reviewer passed the actual shifted maximum iff at frozen source F5AFA259BC027747FD13D286499585898CEDC5FA8F0797D2D6828013FB1E0B41. Review covered q=1/2, a=0/q, positive starts, universal staircase, bounded translated half-tail, singleton frontier, unique incoming parents and the necessity direction. No trajectory or maximum conclusion is a premise. |
| Indexed ancestry and observations | Source/plan task supplied the four separate modules and the [source comparison](../notes/ANCESTRY-OBSERVATION-INTERFACE.md); coordinator integrated their actual printed endpoints. Indexed paths, erased ancestry and recovery/prediction conditions remain distinct. |

Key hashes recorded during independent review. The line-ending normalization
exception below distinguishes review bytes from final receipt bytes:

```text
InfiniteConservation ED609F3A0495893BE4EB7C633B30364EC46D57DCD29F758D53FCB690CAD74D0B
MinimalCrossing AC9EC8A7775262EFAA52D191AEC2B793A3A01D45C1167C3CA7EC435131F63F37
FiniteEditStability DBCD4A3EA5F624F807D0FE7998A0D1A2D8BE79BA23AC4946BF05137491F4D998
PhaseShift 504C71E130463EF9F2DCAC11C77917AA204F42995EE23B722A7DB439C7EA8BE7
FixedGenderLift 2805AB8EF85A018B2276AA137118F0E64990A6358349E7A1B59006D24A50BA7A
SlowAvoidance D6E8E593E81BE4A642C0C2D4BF8266E2AD1A1CEB9ABFD2559C0559B650F5A520
FiniteAvoidance E2AC08FEF95B8CEB6779CB2A656BA9E02C6FCFADAF0E5B81EA57A1A4CC211541
FixedGenderReindex 93953E4E77F092692BC254B52E4D3082459B700EEC5A4259C1560AC0DADDD3E9
PopulationReindex 815951D97E90F9DA0AA83CB0ACD8683FFB1AA3460930B7ECA7FB522E986AE666
RealBridges BDF46750B494B863B0536CD131E4837964800144439B5A4E67926566AEC9EE9A
```

The [older-construction source audit](../notes/OLDER-CONSTRUCTIONS-AND-RANK-AUDIT.md)
corrects the novelty boundary: Alexander's original examples already have
inspecies structure, and his 2013 discussion already names rank and
forbidden-subtree connections. The exact prescribed-target/cap-three
conjunction and new quantitative statements require their own priority review.
The complete height formula is deliberately retained as a conjecture, with
[finite evidence](../research/thue-morse/kernel-conjecture-results.json) and no
universal Lean theorem.

Only line-ending normalization was subsequently applied to InfiniteConservation and QuantitativeAvoidance to match the repository's `*.lean eol=lf` rule. Their Lean tokens are unchanged; the final receipts record the normalized bytes. The InfiniteConservation hash above identifies its pre-normalization file; its final committed SHA-256 is `55B11EAA840F25500428FB41652CA91994019E8D1300C8DF15C978AC46698EE5`. The other hashes listed above match the final receipts.
