# Mathematical handoff

Updated 25 September 2026. This notebook studies the target-dependent
avoiding population in the separate September 2026 classification manuscript,
alongside Samuel A. Alexander's 2013 unavoidability and inspecies papers and
Samuel Allen Alexander's 2026 specieslike-cluster paper. The
[source ledger](SOURCES.md) identifies the exact works and versions. The
[question ledger](QUESTION-LEDGER.md) distinguishes the historical classification
question from follow-ons posed here. No message has been sent to Dr. Alexander.

The main results in all ten proof lanes are now Lean-checked under their stated
models and hypotheses. The [current answers](TEN-SOLUTIONS.md) give the result
map; the [original ten proposals](TEN-RESEARCH-IDEAS.md) remain a historical
question snapshot. The separate literal integer-module 2-regularity wrapper
still awaits compilation; the full height formula and executable binary
recurrence themselves are already checked.

## Results worth reviewing

1. **The fixed-source-gender child-cap threshold is two.** For every binary
   target that is not eventually periodic, a directed line graph of the
   manuscript's $`P_s`$ gives an eligible avoiding population with permanent
   source genders, exactly two children per vertex, and exactly three roots.
   Projection and lifting preserve every infinite word path without changing
   its initial letter. Caps below two are impossible. The same retained graph
   is an inspecies, specieslike, and reflecting. See the
   [threshold proof](notes/CAP-TWO-THRESHOLD.md) and
   [species theorem](notes/CAP-TWO-SPECIES.md). Three-root minimality is not claimed.
2. **Minimum crossing width determines the tail for every finite alphabet.**
   In an actual naturally ordered population with $`k`$ required incoming
   labels and child cap $`k`$, full-degree conservation forces eventual
   regularity and constant crossing width. If that width is eventually
   $`k(k+1)/2`$, the tail edges are exactly $`u\to v`$ with
   $`u<v\le u+k`$. The [general rigidity theorem](notes/GENERAL-RIGIDITY-THEOREM.md)
   requires equality at every sufficiently late cut. It determines adjacency;
   arbitrary edge labels do not automatically give universal word realization.
   The earlier binary fixed-gender minimum-width theorem does give universality.
3. **Actual critical populations admit finite port schedules.**
   [PortEncoding](notes/PORT-ENCODING.md) constructs a legal, fair schedule from
   the original population, with its width equal to the actual finite cut
   cardinality. Decoding recovers exactly every labelled edge whose target is
   on the chosen tail, including edges from earlier sources. If the complete
   schedule is eventually periodic, the checked
   [periodic-schedule theorem](notes/PORT-DYNAMICS-FORMALIZATION.md) realizes
   every infinite word from a fixed finite block of starts. Periodicity is an
   additional hypothesis; finite width alone does not establish it. The encoder
   uses classical finite bijections and makes no canonical or effective
   schedule claim.
4. **The full Thue-Morse matching-height formula is proved.**
   [FullHeight](notes/FULL-HEIGHT-PROOF.md) identifies the attained maximum of
   actual $`P_t`$ matching paths at every natural start, including $`L(0)=1`$.
   [DigitRecurrence](notes/DIGIT-RECURRENCE.md) gives a certified executable
   ten-coordinate integer recursion, with one recursive call per binary digit.
   It includes the sharp $`3L(v)\le8v-1`$ for $`v\ge1`$ and equality exactly
   at $`v=3\cdot2^n-1`$, where $`L(v)=8\cdot2^n-3`$. These are actual graph
   maxima, not extrapolations from the earlier fitted data. No minimality of
   ten coordinates or bit-complexity bound is claimed.
5. **Phase changes have exact extrema and computable heights.** Rebuilding
   the graph from $`t_a(k)=t(k+a)`$ gives $`3L_a(v)\le8v+5a-1`$ for
   $`v\ge1`$, with optimal coefficient $`8/3`$. Equality holds exactly when,
   for a dyadic $`q=2^n`$, $`a\le q`$, $`v=3q-a-1`$, and
   $`L_a(v)=8q-a-3`$. The
   [phase equality theorem](notes/PHASE-EXTREMAL-FORMALIZATION.md) and
   [finite frontier algorithm](notes/PHASE-HEIGHT-FORMALIZATION.md) cover the
   stated equality family and all phase/start maxima respectively. The latter
   includes start zero; it is not a joint phase/index digit formula.
6. **Quantitative aperiodicity supplies explicit upper bounds.** A modulus
   $`M(v,b)`$ locating failures of all relevant periods and antiperiods gives
   $`\ell<B_{v+1}`$ for every matching prefix from $`v`$, where
   $`B_0=0`$ and $`B_{r+1}=M(v,B_r)`$. Uniform window length $`R`$ gives
   $`\ell<(v+1)R`$. Every non-eventually-periodic word has such a modulus;
   its existence proof uses classical choice, while the bound is explicit
   given the modulus. See [QuantitativeModulus](notes/QUANTITATIVE-MODULUS-THEOREM.md).
   Conversely, [FiniteAvoidance](notes/FINITE-AVOIDANCE-FORMALIZATION.md)
   proves that every proposed growth function is exceeded by actual finite
   maxima along increasing starts for a suitable aperiodic target. All starts
   of that target still have finite attained maxima.
7. **Finite edits have exact maxima, a full equality test, and a sharp universal
   constant.** If $`s(k)=t(k)`$ for $`k\ge m`$, then
   $`3L_s(v)\le8v+8m-1`$ for $`v\ge1`$. The integer allowance $`8m-1`$
   is optimal uniformly over all such targets. Equality occurs exactly at
   $`v=3q-m-1`$, $`L_s(v)=8q-3`$, with dyadic $`q\ge m`$, when the first
   $`m`$ target labels follow the explicit all-two-step prefix. A finite
   frontier decomposition gives an exact maximum at every specified start,
   including early extinction and zero. See
   [FiniteEditExact](notes/FINITE-EDIT-EXACT-FORMALIZATION.md). A particular
   edited target can have a smaller best additive constant; its global
   classification remains separate.
8. **Productive pruning preserves the entire infinite word language.**
   [ProductiveCore](notes/PRODUCTIVE-CORE-THEOREM.md) constructs an eligible
   binary population on the actual productive subtype, preserves any supplied
   child cap, and proves realization of a word before pruning iff realization
   afterward. Whole-graph IAP makes the core an inspecies. For natural birth
   order, unrestricted maximal specieslike clusters are descendant-closed;
   common-ancestor/reflection-constrained maxima need not be. Pruning commutes
   in both settings by their respective proved hypotheses, with explicit
   counterexamples to removing those hypotheses. Finite paths need not survive.
9. **Finite-boundary repair has an exact existence and optimality criterion.**
   On a fixed infinite retained subset of a binary population, an eligible
   deletion-only repair exists iff finitely many retained vertices lack an
   incoming label. The canonical repair deletes all remaining incoming edges
   at exactly those deficient vertices, keeps the greatest admissible edge
   relation, and has the smallest admissible root set. It preserves child caps
   and avoidance. [BoundaryRepair](notes/BOUNDARY-REPAIR-THEOREM.md) also
   computes both source-cone repairs: one disconnects, so eligibility repair
   does not generally preserve specieslike connectedness.
10. **A complete stateful CA certificate strictly improves its static family.**
    For an explicit three-state rule, every valid fixed two-label static
    certificate has optimal east support exactly one. A state potential
    rules out every exact translational recurrence with nonzero horizontal
    displacement for finite nonempty initial configurations, with a full
    two-cell oscillator checked as well. [StatefulCA](notes/STATEFUL-CA-FORMALIZATION.md)
    proves the rule-to-trajectory result, and
    [StatefulCAReal](notes/STATEFUL-CA-REAL.md) proves the attained static optimum
    over Mathlib's literal real convex hulls. This is a synthetic same-rule
    separation, not an improved speed bound for a published or binary Life-like rule.

## Formal and source scope

The package also constructs birth-order enumerations, proves the positive
binary theorem, transports the binary classification to actual real birthdates,
and checks general IAP/root-cone and degree/root interfaces. The default core
is Std-only; optional Mathlib modules include the actual population encoder
and real convex-hull comparison. The latter two have passed standalone Lean
checks; repository-wide integration receipts are recorded separately in
[FORMALIZATION.md](FORMALIZATION.md) and [STATUS.md](STATUS.md).

The proved binary recursion must be distinguished from the optional
[`DigitRegularity` wrapper](real/DigitRegularity.lean): its statement that the
integer span of the full 2-kernel is finitely generated has passed a mathematical
statement review, but compilation is still pending in this handoff. No checked
wrapper claim is made here.

Attribution is part of the result. Alexander's 2013 unavoidability paper supplies
the population axioms, the eventually-periodic positive theorem, and the
historical classification question. The separate September 2026 manuscript
supplies the target-dependent $`P_s`$ construction and the classification;
these are not discoveries of this notebook. Alexander's 2013 inspecies results
already supply cofinite descendants, and his 2026 Example 14 supplies earlier
root-cone patterns. The [older-construction audit](notes/OLDER-CONSTRUCTIONS-AND-RANK-AUDIT.md)
and [prior-work ledger](PRIOR-WORK-AUDIT.md) preserve those distinctions.

The methods also have established antecedents: Harary and Norman and later
Orlin for line digraphs; Mateus de Oliveira Oliveira for finite-frontier slice
encodings; Young, Tarjan, and Orlin for graph potentials, with Karp and
Dasdan and Gupta for cycle-mean methods. See the
[line-digraph audit](notes/source-audits/LINE-GRAPH-PRIOR-ART-AUDIT.md) and
[port/CA source comparison](notes/source-audits/PROPOSALS3-10-SOURCE-AUDIT.md).
The precise model corollaries and quantitative formulas are the results to
assess. Bounded literature searches do not certify their priority, and the
classification source remains a manuscript rather than a refereed publication.

Useful external feedback now concerns equivalent earlier height formulas or
recurrences, optimal root counts, structure beyond minimum crossing width,
joint phase/index formulas, individual edited-target constants, and improvements
for natural CA rules. Mathematical verification does not establish empirical
species boundaries or reveal what an author has considered privately. The
repository owner can adapt the [outreach draft](OUTREACH-DRAFT.md); sending it
is a separate action.
