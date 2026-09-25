# Ten research proposals for Alexander's genealogy and word problems

These are ten precise proposals for discussion, not ten claims of established
originality. We cannot know which ideas Alexander has considered privately.
The intended standard is a useful mathematical question, a credible route into
it, and an explicit distinction between a checked seed and an unproved extension.
The final formalization receipts determine which seeds have passed Lean.

The principal sources are Alexander's [2013 population and unavoidability
paper](https://arxiv.org/html/1212.0186v2), his [2013 inspecies
paper](https://arxiv.org/html/1201.2869), his [2026 specieslike-cluster
paper](https://arxiv.org/html/2602.05274v1), and the [September 2026 classification
manuscript](https://github.com/avg-netizen/biological-unavoidability/blob/main/paper.md).
The latter already asks for useful quantitative fixed-target bounds. The
proposals below specialize or connect these questions; they are not evidence
that the surrounding fields have received little mathematical effort.

## 1. Is two or three the true fixed-gender threshold?

**Question.** For an aperiodic binary word $`s`$, define $`d_{\mathrm{vertex}}(s)`$ to be the
least uniform child cap among eligible populations avoiding $`s`$ in which gender
belongs permanently to each vertex. Is $`d_{\mathrm{vertex}}(s)=2`$ for every such $`s`$, or
does some word require three children? A particularly clean test case is the
Thue–Morse word.

**New seed.** The source's two-copy lift has child cap four. Retaining only
copies whose gender labels an outgoing base edge lowers this to
three: every odd target index retains exactly one copy, every even target
index retains at most two, and a base vertex has at most one child index of
each parity. Every parent of a retained vertex is itself retained. The
resulting productive core also has cofinite descendants at every vertex,
which makes its whole graph an inspecies. The [productive-core
formalization](lean/SamuelAlexanderResearch/FixedGenderLift.lean) and its scope
note record the checked version. The [retained-vertex adapter](lean/SamuelAlexanderResearch/FixedGenderReindex.lean)
also proves the unconditional fixed-gender cap-three classification. This
does not establish the cap-two case. Alexander's earlier $`T_h`$ and $`H_h`$
constructions already have whole-graph inspecies structure; the distinction
here is a **prescribed arbitrary aperiodic target with a uniform cap three**.
Their varying outdegrees do not already give this uniform bound; see the
[exact source comparison](notes/OLDER-CONSTRUCTIONS-AND-RANK-AUDIT.md).

**Why pursue it.** This reduces a model distinction to one integer. It also
connects an extremal offspring question with Alexander's older minimal
ancestrally closed sets. A successful answer would improve a construction or
prove a structural obstruction, both useful outcomes.

**First decisive test.** Search cap-two populations through their bounded
crossing edges, while enforcing permanent source genders and both incoming
genders exactly. Use the conservation and discrepancy constraints to reject
impossible partial constructions. A finite candidate must come with an
infinite extension rule and an avoidance proof; a finite failed search is not
an impossibility result. Priority checking must specifically cover pruning
variants of the source lift, not just its displayed cap-four statement.

## 2. Classify the populations with the smallest possible crossing count

**Proposed theorem.** Suppose every nonroot requires $`k`$ distinct incoming
labels, every vertex has at most $`k`$ children, and the eventual crossing count
is exactly $`\frac{k(k+1)}{2}`$. Is the graph, outside a finite prefix in birth order,
necessarily the directed $`k`$th power of a ray: precisely the edges
$`v\to v+1,\ldots,v+k`$?

**Checked seed.** The [infinite conservation
module](lean/SamuelAlexanderResearch/InfiniteConservation.lean) proves
$`C_N\ge\frac{k(k+1)}{2}`$ after all roots, and proves eventual full indegree and
outdegree $`k`$ and constant $`C_N`$ at the critical child cap. The triangular
bound counts incoming edges to the first $`k`$ vertices after a cut. The
[binary equality analysis](lean/SamuelAlexanderResearch/MinimalCrossing.lean)
is now checked: width three on every cut of a tail forces exactly the $`+1,+2`$
edges there. Permanent source genders force alternating genders and universal
word realization. Consequently an avoiding critical fixed-gender population
has eventual **crossing width** at least four. This is not a four-child bound.
The general-$`k`$ rigidity statement remains open in this project.

**Why pursue it.** An extremal numerical inequality could determine the
entire eventual genealogy. In the binary case it would explain why the
source's $`+1,+2`$ geometry is canonical at width three. For permanent binary
genders that geometry forces alternating vertex genders and realizes every
word, so a cap-two fixed-gender avoider would need crossing width at least four.

**Next decisive test.** Generalize the checked binary block-equality argument
to arbitrary $`k`$. A counterexample must
retain simplicity, full degrees, the same birth ordering, and constant
minimal width. Omitting any of those changes the question.

## 3. Turn critical populations into a finite-port description

**Target.** Give an exact representation of every critical population tail as
a sequence of updates to a fixed finite collection of crossing-edge ports.
Each birth consumes its $`k`$ incoming ports and creates its $`k`$ outgoing ports.
The data must retain labels, source identities needed for simplicity, and the
order in which pending edges terminate.

**Conjectural consequence.** If this complete update description is eventually
periodic, every infinite label word is realizable. Finite control and a
periodic schedule should give a finite-state description of the word language;
Alexander's positive theorem then supplies all eventually periodic words.
The usual finite-state witness or compactness argument should force the full
word language. This needs a genuine graph-to-language proof: a finite number
of ports alone does not make an arbitrary update sequence periodic or
finite-state.

**Why pursue it.** It would locate where an avoiding population stores its
nonperiodic information. The checked degree theorem supplies a finite number
of ports, while the source construction supplies an aperiodic schedule of
labels. The distinction is sharper than saying that the graph is complicated.

**First decisive test.** Specify reversible encoding and decoding for the
binary width-three and width-four cases. Prove that paths and labels are
preserved. Only then implement finite-state language checks for periodic
schedules. Finite automata and bounded-width graph methods are established
ingredients; the research target is this precise population representation.

## 4. Find a finite binary-digit description of the entire sharp-length function

**Question.** Is the sequence of exact maxima $`L(v)`$ in the Thue–Morse avoiding
graph 2-regular, or does it admit another finite system of recurrences on
binary digits? Here 2-regular means that the integer module generated by
the subsequences $`L(2^e n+r)`$, for $`e\ge0`$ and $`0\le r<2^e`$, is finitely generated.
This is a specific conjecture, not an inference from the input word being
automatic.

**Checked seed.** The interval theorem reduces $`L(v)+1`$ to the first
coalescence of two neighboring boundary trajectories. The sharp bound and its
exact equality family are checked. The [first-hit
corollaries](lean/SamuelAlexanderResearch/SharpCorollaries.lean) additionally
describe the simpler baseline hitting-time function exactly. They do not
describe all neighboring-pair coalescence times, which is the missing object.
There is now a precise [closed-form and ten-coordinate recurrence
candidate](research/thue-morse/FULL-HEIGHT-CONJECTURE.md), using binary parity
and the 2-adic valuation of $`\lfloor v/2\rfloor+1`$. Its [independent finite
check](research/thue-morse/kernel-conjecture-results.json) passes every stored
positive start below 131,072, 16,384 full coordinate transitions and 2,200 fresh
frontier computations. Fourteen deliberately long cases hit the finite cap
and are explicitly recorded as skipped. None of this proves the formula.

**Why pursue it.** A finite recursion would explain the irregular values
between the dyadic equality starts and allow exact evaluation at enormous
indices using their digits. A proof of nonregularity would also reveal a
surprising complexity gap between the word and its matching geometry.

**Next decisive test.** Prove the candidate's finite high-bit cases by induction
over actual dyadic blocks, as in the sharp proof. The fitting and fresh-index
falsification have already supplied a concrete target. Automatic-sequence
algorithms and Thue-Morse matching literature
are close prior work, so the coalescence function must be distinguished from
ordinary longest common subsequences.

## 5. Understand how the sharp theorem changes with the word's phase

**Question.** For $`s_a(k)=t(k+a)`$, form its own avoiding graph $`P_{s_a}`$ and let
$`L_a(v)`$ be the longest match to $`s_a`$ from $`v`$. Find useful joint bounds,
equality families, or a digit recursion in $`(a,v)`$. In particular, determine
whether the optimal leading coefficient in $`v`$ is independent of each fixed
phase $`a`$, and how the additive allowance depends on $`a`$.

**Model detail.** Both the target and its graph change. The graph's row color
is $`t(w+2a)`$, by the even/odd identities. Keeping $`P_t`$ fixed and merely shifting
the target is a different and often trivial problem: its consecutive edges
already spell tails $`t(a),t(a+1),\ldots`$ for $`a\ge2`$.

**Why pursue it.** The original sharp theorem has a privileged phase-zero
baseline. A phase theorem would tell us which part of its $`\frac{8}{3}`$ constant comes
from substitution structure and which part comes from that origin choice.

**Checked progress.** [PhaseShift](lean/SamuelAlexanderResearch/PhaseShift.lean)
proves $`3L_a(v)\le8v+5a-1`$ for positive starts and actual long dyadic witnesses
with their starts in a bounded interval. [RealBridges](real/RealBridges.lean)
proves that the leading coefficient is exactly $`\frac{8}{3}`$ for every fixed phase,
against all smaller real coefficients and all real additive constants. A
recursive actual extremal path now proves the complete equality set:
$`3L_a(v)=8v+5a-1`$ holds exactly when $`v=3\cdot2^n-a-1`$ and $`a\le2^n`$, with
$`L_a(v)=8\cdot2^n-a-3`$. The [formalization note](notes/PHASE-EXTREMAL-FORMALIZATION.md)
records the construction and uniqueness argument. Joint digit recurrences
remain open.

**First decisive test.** Adapt the exact interval checker to $`\operatorname{row}(s_a)`$ and
$`s_a`$, and inspect dyadic phase classes. A successful proof should transport
the existing descent argument or identify precisely why a new descent is
needed. The phase-zero result is an input, not a proof of phase invariance.

## 6. Relate avoidance length to a quantitative failure of periodicity

**Target.** Replace qualitative aperiodicity with a function measuring how
long a word can imitate a period or an antiperiod, and derive matching upper
and lower bounds for $`L_s(v)`$ in $`P_s`$. The offset proof suggests that the
relevant comparisons have small shifts determined by the starting offset.

**Checked seed.** The [quantitative
module](lean/SamuelAlexanderResearch/QuantitativeAvoidance.lean) proves that
if $`s(k+p)=s(k)`$ for $`k<\ell`$, then the explicit two-step path starting at
$`2p-1`$ matches $`\ell`$ edges. Thus very long periodic prefixes create very long
matches even when the full word is aperiodic. Aperiodicity alone supplies
finiteness, not a useful numerical rate.

**New checked theorem.** For every $`f:\mathbb{N}\to\mathbb{N}`$, there is an aperiodic
target whose actual finite maxima exceed $`f(v)`$ at strictly increasing starts.
[SlowAvoidance](lean/SamuelAlexanderResearch/SlowAvoidance.lean) constructs
coherent repeated prefixes separated by long zero blocks ending in one;
[FiniteAvoidance](lean/SamuelAlexanderResearch/FiniteAvoidance.lean) proves
maximum existence at every start and the full quantitative conclusion. The
word construction is executable relative to $`f`$; no separate Turing-machine
computability predicate is formalized. The next question is a useful upper
bound from an explicit modulus of failure of periodicity.

**Why pursue it.** This would separate genuinely quantitative structure, such
as Thue–Morse substitution identities, from qualitative unavoidability. The
first useful result is an explicit modulus-to-bound theorem, followed by a
sharpness construction, not a generic assertion that aperiodic words are
unpredictable.

## 7. Test whether the sharp coefficient survives finite edits

**Question.** If $`s`$ differs from Thue–Morse at only finitely many positions,
does the optimal leading coefficient of $`L_s(v)`$ remain $`\frac{8}{3}`$? More explicitly,
does an edit-dependent constant $`B`$ give $`3L_s(v)\le8v+B`$ for all positive
starts, and is every smaller leading coefficient impossible? Upper stability
and lower sharpness are separate assertions.

**New checked theorem.** If $`s(k)=t(k)`$ for every $`k\ge m`$, then
$`3L_s(v)\le8v+8m-1`$ at every positive start. Generic finite-path transport
preserves length and moves the start by at most $`m`$; transporting the actual
old dyadic equality witnesses proves lower sharpness as well. The
[finite-edit module](lean/SamuelAlexanderResearch/FiniteEditStability.lean)
includes attained maxima and arbitrarily late lower witnesses.
[RealBridges](real/RealBridges.lean) excludes every coefficient below $`\frac{8}{3}`$,
even with any real additive constant. Here $`m`$ bounds the edited initial
segment, rather than counting arbitrarily positioned changed bits.

**Why pursue it.** A positive answer would make $`\frac{8}{3}`$ an invariant of an
eventual substitution pattern; a negative answer would exhibit sensitivity
to finitely much initial information. Either outcome clarifies what the
constant measures.

**Next decisive test.** Determine the best additive constant for each finite
edit and characterize its equality starts. The leading coefficient question
is now proved in this project; the finer finite-prefix dependence is not.

## 8. Develop a productive-core theorem for specieslike populations

**Target.** For an eligible population with whole-graph IAP, retain precisely
the vertices with infinitely many strict descendants. Prove that the induced
core is an eligible population, is an inspecies as a whole, and preserves
avoidance and the child cap. Then determine how this operation acts on the
maximal specieslike clusters of a general ambient population.

**Reasoning to test.** Every ancestor of a productive vertex is productive,
so incoming-parent coverage survives restriction. Finite roots and finite
branching should ensure an infinite productive core. Whole-graph IAP then
makes each productive vertex's descendants cofinite, connecting to the
checked finite/cofinite criterion and Alexander's 2013 Proposition 6. The
specific three-child construction in proposal 1 is a useful test instance.

**Why pursue it.** It would separate terminal material from the part carrying
indefinite ancestry, and explain exactly when the 2026 specieslike notion
reduces to the older inspecies notion. The cluster behavior is the difficult
extension: pruning relative to the whole ambient graph need not agree with
pruning inside a chosen cluster.

**First decisive test.** Prove the whole-population theorem with all root,
finiteness, and induced-edge obligations explicit. Then seek a small example
where local and ambient cores disagree. Productive-state pruning and
König's lemma are classical; novelty would concern the precise simultaneous
preservation and cluster theorem, not pruning as an abstract operation.

## 9. Measure the cost of repairing parent labels at a cluster boundary

**Target.** Given a specieslike or common-ancestor subset, quantify the
missing incoming labels in its induced graph and find minimal repairs that
restore eligibility while preserving avoidance. Repairs may remove edges
or declare newly parentless vertices to be roots; adding arbitrary edges
can create new word paths and requires a separate analysis.

**First theorem to try.** For a cofinite induced subset, only finitely many
retained vertices can have lost a parent, because finitely many removed
vertices have finitely many children. Delete all incoming edges at those
deficient vertices. This creates only finitely many new roots and preserves
avoidance by edge deletion. Prove the full population statement, then ask
when connectedness, IAP, or a preferred cluster interpretation survives.

**Why pursue it.** Alexander's maximal common-ancestor cones and his
label-coverage model interact at their boundaries: a cone can be a valid
ancestry cluster while failing the parent-label hypotheses. A repair theorem
would turn that obstruction into a controlled interface. Whole-population
common ancestry cannot be retained in an eligible binary population, by the
checked two-root obstruction, so a repair must state which cluster property
it changes.

**First decisive test.** Work out exact minimum repairs for the two cones of
$`P_s`$, then for a general finite boundary. An optimization formulation must
include the newly created roots and the loss of connectivity; counting missing
labels alone does not capture the problem.

## 10. Find a stateful cellular-automaton certificate that improves the static bound

**Target.** Replace fixed displacement sets for parent labels with a finite
state or phase graph. A transition records the selected parent label, its
displacement, and the next admissible state. For a direction $`u`$, seek a
potential $`h`$ and bound $`c`$ such that every permitted transition $`q\to q^{\prime}`$
with displacement $`d`$ satisfies $`u\cdot d\le c+h(q)-h(q^{\prime})`$. Summing along a lifeline
telescopes the potential and yields a directional speed bound.

**Why the state matters.** The existing static certificate gives an
intersection of convex hulls from constant-label lifelines; averaging fixed
label sets cannot improve it. A state graph can forbid high-displacement
steps from following one another. The research target is a valid local-rule
certificate for which this additional restriction strictly improves that
same-rule static intersection and survives comparison with published speed
limits.

**First decisive test.** Start with a small anisotropic rule and an exact
truth-table certificate. Verify every state transition and prove that every
constructed infinite lifeline follows the state graph. Then check the
potential inequalities with rational arithmetic. A state graph fitted only
to observed trajectories does not certify unobserved evolution.

**Prior-work boundary.** Cycle-mean bounds, telescoping potentials, and
finite-state restrictions are established tools. Alexander's cellular-
automaton application and Johnston's [Life-like speed
bounds](https://arxiv.org/abs/1203.1644) are direct prior work. A new contribution
would be an explicit stronger rule-specific certificate with a proof of its
scope, not the general potential method.

## Suggested order of attack

The strongest next proof targets are the exact full-height formula in proposal
4, general-$`k`$ rigidity in proposal 2, and the cap-two obstruction/construction
in proposal 1. Proposals 5, 6 and 7 now contain proved quantitative results;
their remaining questions are explicitly narrower. Proposals 3, 8 and 9 seek
structural generalizations. Proposal 10 needs an actual improvement for a
specified cellular-automaton rule. Alexander's 2013 Section 6 already mentions
forbidden-subtree universality and graph-rank theory, so those are relevant
existing connections rather than discoveries of this notebook.
