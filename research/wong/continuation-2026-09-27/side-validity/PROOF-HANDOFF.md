# Side proof handoff: measurability of valid marked histories

Status: complete mathematical argument and executable finite sanity check.
The argument below is NOT a Lean-checked theorem. No main-repository file,
build, Git state, or audit receipt has been changed by this side conversation.

This packet addresses one helper step only: upgrading almost-sure validity
on the random-input space to almost-sure validity under the output history
law. The main chat owns integration, compilation, and source correspondence.

## Observed checkpoint and exact target

The inspected main task is "Formalize Wong ARG and ancestry",
thread 01a0e0ce-445a-7b82-9846-86623ccf3a73. Its source changes and build output
were inspected through the task reader, not by rerunning its builds.
The latest inspected task timestamp is 2026-09-27T03:56:54Z.
The checkout is C:/Users/Owner/Documents/Codex/2026-09-27/wong-alexander.

The current construction already has:
- WongMarkedProcess.law_ae_good and its stopped-recorder consequences.
- WongMarkedMeasurable.measurable_stoppedRecord.
- WongMarkedDated.measurable_realize and history_count_time_projection.
- WongMarkedDated.law_ae_realize_validDated on the input probability space.

The former attempted historyLaw_ae_validDated statement was replaced with the
input-space statement because transferring an arbitrary predicate through
ae_map_iff requires its measurable-set hypothesis. This note supplies the
mathematical route to that hypothesis. The main task is already working on
that integration; this is a helper argument, not a competing implementation.

The needed endpoints are:
1. Coverage over all real genome positions iff finite endpoint tests.
2. MeasurableSet {s : RawState Real | Valid n lo hi s}.
3. MeasurableSet {h : History | ValidDated L n h}.
4. historyLaw_ae_validDated by the existing input-space theorem and ae_map_iff.

## Finite endpoint theorem

Fix a finite family of half-open intervals [a_i,b_i), with distinct slot IDs
i = 0,...,N-1. Let child_i be each slot's child vertex. No distinctness of
endpoints is assumed. Repeated intervals retain their different IDs.

For a vertex v and position x, define

    A(v,x) = { i < N : child_i = v and a_i <= x < b_i }.

Define the finite test set

    E = {lo} union {a_i,b_i : i < N}.

Then, for each vertex v,

    (for every x in [lo,hi), A(v,x) has exactly one member)

is equivalent to

    (for every e in E intersect [lo,hi), A(v,e) has exactly one member).

This also covers the empty genome interval vacuously.

### Proof, including the breakpoint boundary case

The forward implication is immediate.

For the converse, take any x with lo <= x < hi. Because lo is in E and
lo <= x, the finite set {e in E : e <= x} is nonempty. Let y be its greatest
member. Thus y is in E and lo <= y <= x < hi.

For every allocated slot i,

    a_i <= x < b_i  iff  a_i <= y < b_i.

If the interval contains x, its left endpoint a_i is in E and at most x,
so a_i <= y. Also y <= x < b_i.

Conversely, suppose it contains y. Then a_i <= y <= x. If x >= b_i, the
right endpoint b_i would be an element of E at most x, and maximality of y
would give b_i <= y, contradicting y < b_i. Hence x < b_i.

Therefore A(v,x) and A(v,y) are literally the same set of slot IDs. The
endpoint hypothesis gives exactly one member at y, so also at x.

Coincident endpoints cause no difficulty. At a shared endpoint c, a slot
ending at c is excluded and a slot starting at c is included, exactly as
required by half-open intervals. The argument never identifies two slots
merely because their endpoints coincide.

## Applying it to RawState.Valid

For the recorder's state s, take:
- N = s.nextLineage;
- a_i = (s.slot i).interval.lo;
- b_i = (s.slot i).interval.hi;
- child_i = (s.slot i).child.

Use ALL allocated slots, including active ones. Testing only completed
graph edges would not match the actual coverage invariant.

The uncountable coverage field in Valid becomes the following countable
formula. Write U(s,v,x) for the exactly-one-slot predicate above.

    for every natural v < s.nextVertex:
      if lo < hi, U(s,v,lo);
      for every natural j < s.nextLineage:
        if lo <= a_j < hi, U(s,v,a_j);
        if lo <= b_j < hi, U(s,v,b_j).

Each U is itself expressible with natural-number quantifiers:

    exists i:
      i < N and child_i = v and a_i <= x < b_i
      and for every j:
        (j < N and child_j = v and a_j <= x < b_j) implies j = i.

All coordinate comparisons are Borel measurable in the recorder's explicit
coding. At the variable test position x = a_j or b_j they remain comparisons
between measurable real coordinates. The countable unions/intersections for
the natural-number quantifiers preserve measurability.

Every other field of Valid uses countable discrete data, real comparisons,
or natural-number quantification:
- vertex count versus event-list length;
- active-ID bounds;
- child and interval bounds;
- completed-parent order;
- completed-parent exclusion from the sampled vertices.

Membership in completed is simply i < nextLineage and i not in active.
Consequently {s | Valid n lo hi s} is a measurable set.

No probability assumption is used in this proof.

## From state validity to dated-history validity

The apparent existential over arbitrary RawState values in ValidDated is
uniquely pinned down by h.result = some s. Eliminate it by case distinction
on the measurable Option result, using the already supplied measurable
getD/default-state map in the successful case.

The remaining conditions are measurable:
- h.states h.horizon uses evaluation at a natural-number random index;
- equality of states follows through the injective stateCode and its
  countable coordinate equalities;
- Valid is measurable by the endpoint theorem;
- frontier size, event count, and vertex count are measurable;
- constant tails quantify only over natural indices;
- completed-edge chronology uses measurable real comparisons and
  evaluation of stored dates at natural-number indices.

For state equality, include ALL fields in stateCode, including the total
slot and parent functions and the event list. Their encodings use countably
many coordinates. Do not silently replace equality of RawState values by
equality of only their allocated graph edges.

Thus {h | ValidDated L n h} is measurable in the existing History coding.

After that lemma, the output-law theorem is the following short application
of the already checked input-space theorem (template, not compiler-checked):

    unfold historyLaw
    exact (ae_map_iff
      (measurable_realize L hL n a b).aemeasurable
      (measurableSet_validDated L n)).2
        (law_ae_realize_validDated L hL n hn a b ha hb)

Use the same normalizedRatio a b ha hb and all parameter assumptions as in
law_ae_realize_validDated. This changes where the validity assertion lives;
it does not change the stochastic model.

## Why both sides of every interval are tested

Testing only left endpoints is insufficient. The intervals [0,2) and [6,8)
each pass a unique-coverage test at their left endpoints, but leave a gap
inside the genome [0,8). Testing the right endpoint 2 detects it.

A fixed set of observed biological loci is also different from this test
set: E depends on the full recorded graph. The theorem does not say that a
limited genome observation identifies the full graph, a pedigree, or a
species-like cluster.

## Executed sanity checks and scope

endpoint-coverage-check.js is self-contained and can be run with Node:

    node endpoint-coverage-check.js

The exact saved script was evaluated in the tool's JavaScript runtime.
It checked all 11,111 ordered interval families of size at most four drawn
from the ten proper intervals on {0,2,4,6,8}, plus six explicit boundary
cases. Repeated intervals count as distinct slots. In total it checked
310,264 slot-membership comparisons between cell probes and their left
endpoint representative.

The boundary cases include adjacent intervals, duplicate slots, a gap,
overlap, endpoints outside the genome, and an empty interval family.
It also confirms that the left-endpoints-only test misses the stated gap.

These finite checks are supporting evidence for the elementary argument.
They are NOT a Lean proof, a validation of the main repository, a source
correspondence audit, or a substitute for an exact-commit combined receipt.

## Shortest next route and stopping condition

The main owner can use its existing breakpoint-cell machinery if compatible
with allocated slots; otherwise the finite-floor proof above is sufficient.
Formalize the endpoint equivalence, derive the two measurable predicates,
and apply ae_map_iff. Compile and audit these endpoints in the main owner's
normal single-writer verification flow at a stable commit.

This side contribution stops at the handoff. It does not start a second
implementation, run the main build, or modify shared audit or ledger files.

