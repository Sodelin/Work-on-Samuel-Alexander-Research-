Independent combined statement review, 2026-09-27.

Disposition: the stated raw-recorder/count-time pushforward theorems survive
this bounded read-only review. One concrete counterexample exposed an
important stronger claim that those theorems do not establish: elapsed time
cannot be projected from the undated stopped `RawState` alone. The parent
accepted the finding and added a separately stored dated-history object.
The dated factorization and the final measurable output-validity theorem have
now passed module compilation. This reviewer inspected their existing compiler
evidence; exact-commit integration remains the root lane's separate gate.
No compiler was run for these independent reviews.

Reviewed source snapshots:

| File | SHA-256 |
|---|---|
| `real/WongMarkedLaw.lean` | `42e61509f5ce72ed978999af1207afab8fb87488aa4729be111b95fddfe6dca1` |
| `real/WongMarkedProcess.lean` | `e446107206deea5cd84b4bc4ccc8f852c00c73a14fc0975453871920d3ea92d0` |
| `real/WongMarkedRecorder.lean` | `1dcec9e5522f03adf21a308bd31a64a5f10a445b567bc72701916009972bdfea` |

The review also read the definitions of `totalRate`, `rawWait`, `eventTime`,
`normalizedRatio`, and literal jump masses in the pre-existing waiting/count
modules. Source-rate correspondence was cross-checked against the source-audit
lane's primary-source contract, `source-audit/APPENDIX-B-CONTRACT.md`.
No compiler was invoked, no stable module was edited, and this note does not
replace an exact-commit compiler receipt.

**Concrete attempted falsification: erase the clock and ask the graph for time.**

Take `L = 1`, `n = 2`, merger scale `a = 1`, recombination scale `b = 0`, and
the legal count path `K = (2,1,1,...)`. At the used spatial coordinate choose
the merger pair `{0,1}` and any interior cut, for example `1/2`. Use identical
spatial arrays and count paths in two samples. Change only the first unit
exponential innovation: use `E(0)=1` in the first sample and `E(0)=2` in the
second. Other clock values can remain identical and positive.

`recordPrefix` never reads the clock coordinate, so both samples produce the
same stopped raw state: exactly one merger, the same fresh vertex/lineage, the
same two completed records, and one terminal active lineage. At count two,
`totalRate 1 0 2 = 1`. Consequently the first `recordedTime` is respectively
1 and 2. A function of the undated stopped raw state alone therefore cannot
return both answers.

This falsifies a proposed factorization through the final undated graph. It
does **not** falsify `recorded_count_time_projection`: that theorem applies
`recordObservation` to the original sample, and `recordedTime` intentionally
uses its external clock path. It also does not assert that either singleton
sample has positive probability under a continuous law; singleton mass is
irrelevant to the demonstrated pointwise factorization failure.

The parent's proposed repair is appropriate: a finite stopped marked-history
encoding stores horizon J, the actual recorded prefix-state snapshots capped
at J, and their event-time labels. Its projection can then read frontier
cardinalities and timestamps from the stored value alone. This is redundant
but faithful; efficient serialization is a separate claim. Two acceptance
details were sent to the parent:

1. Fresh event vertex `n+j` must receive time `eventTime(j+1)`. `eventTime(0)`
   is the initial zero sample time, not the first event date.
2. The nonhitting default `firstHit=0` must not silently turn a failed stopped
   record into a successful dated initial history. Preserve a failure flag or
   an `Option` guard, or explicitly limit success claims to the proven
   almost-sure Good event.

**The count projection actually checks the generated frontier.**

`recordedCount` obtains a prefix through the actual `recordPrefix` recursion
and reads `s.active.card`; it does not directly return the driving count.
`step_valid_count` proves the split and merger updates change that cardinality
by exactly +1 and -1. `prefix_valid_count` carries this invariant from the
initial n distinct lineage IDs through every pre-hit prefix. It separately
proves `s.events.length=t`. Thus the key equality is supported by a real
recorder invariant, not asserted by storing an unexplained count field.

`recordedTime` reads the actual event-log length but evaluates the independently
constructed `eventTime` at that length. That is a genuine check of the number
of generated events, with the time-factorization limit identified above.
`recorded_count_time_projection` obtains almost-sure equality of the entire
computed count/time paths, then applies `Measure.map_congr` and the product
marginal theorem. `recordObservation_aemeasurable` is an additional safeguard:
the map equality is not being marketed as a zero pushforward from an
unmeasurable arbitrary observation.

**Malformed inputs and boundary cases.**

The precise rejection behavior is local to the consumed history:

- An incorrect initial count, `n=0`, or a nonhitting count path causes
  `stoppedRecord` to return `none`.
- A consumed count jump other than +1 or -1, an absent selected split lineage,
  an invalid split cut, or a merger selection that is not a two-element subset
  of the current frontier causes the fold to return `none`. `Option.bind`
  propagates that failure.
- Unused mark components are intentionally ignored. A merger does not use its
  split-lineage or cut coordinate, and a split does not use its pair coordinate.
- Post-absorption count entries and marks are intentionally ignored. In
  particular `n=1`, `K(0)=1` yields the initial zero-event record even if an
  unused later count is malformed. Therefore the unqualified sentence
  "every malformed path or mark is rejected" would be too strong.
- Raw graph recording does not validate clock positivity. Positivity and
  increasing pre-hit dates follow almost surely from the source law and the
  positive-rate hypotheses; they are not universal properties of arbitrary
  ambient clock inputs.

The theorems quantify over every finite natural `n` with `0<n`, not just two
samples. Count one stops immediately and produces no artificial final event.
The recombination rate zero boundary is admitted. No deterministic common
bound on event number or elapsed time is asserted.

**Rates and spatial marks.**

The formal event intensity is

`q(k) = b*k + a*k*(k-1)/2`, with `a>0` and `b>=0` for the physical-rate results.

`normalizedRatio a b = 2*b/a`; its upward and downward kernel masses agree
with the corresponding rate divided by q(k). In the source normalization,
`a=1`, `b=rho`, so the count parameter is `theta=2*rho`, not `rho`.
The generic `recorded_count_time_projection` permits arbitrary independent
parameters `theta,a,b` because it proves an equality between two constructions.
Calling it the source-rate law requires the stated specialization; the
`law_ae_finite_physical_graph` theorem makes that specialization explicitly.

`markLaw` samples a uniform active lineage, a uniform unordered two-element
active subset, and an independent normalized Lebesgue breakpoint in `(0,L)`.
The cut density statement is exact. This is the named continuous-coordinate
Big-ARG specialization, not the discrete-link law of the paper's finite-site
illustration. Likewise the per-lineage rate b is a total whole-genome rate in
this parameterization, not an unmentioned per-unit-length intensity.

The index `(event number, active set)` is important: revisiting an active set
at a different event does not reuse the same innovation. Product independence
and the deterministic-index marginal by themselves are not a proof of the
law at a history-selected active set. The separate adaptive-law work must use
the actual prefix's causality and measurability to show that the selected
fresh-row mark has `markLaw` for its current frontier, conditionally on the
recorded past. The reviewed process explicitly disclaims that stronger result;
this review does not count the in-progress adaptive lift as proved.

An attempted alternative objection was to split a lineage at a breakpoint
outside the interval currently reaching its child. That objection does not
apply to this Big-ARG recorder: the incoming slot records what reaches the
child, while the newly created genome receives a full-span partition.
`split_outside_inherited_interval` explicitly checks the behavior. Replacing
this with interval truncation would change the intended pre-resolution
process toward a different ancestral-material process.

**Shared endpoints and the decoder.**

The concrete `reunion` witness performs split then immediate merger. Its two
completed lineages have IDs 2 and 3, both parent 3 and child 2, but complementary
intervals `[lo,cut)` and `[cut,hi)`. Selection is by lineage ID, so the two
lineages are legal distinct merger inputs. `rawRecord_identity_injective`
preserves their identities; `completedRecord_injective` proves that projection
to the finite raw edge records cannot collapse distinct completed slots under
the exact-coverage invariant.

`raw_records_injective` proves unrestricted injectivity of `specRecords` for
one `ParentSpec`, including equal-parent crossovers. Its argument recovers the
raw interior endpoint, which local-parent semantics alone cannot recover.
`rawEncodingEquiv` is a genuine two-sided equivalence to the explicit encoding
range, with no distinct-parent assumption. `reunion_encoded_records` connects
the actual recorder's output to that encoding, so the witness is not an
unrelated hand-constructed `ParentSpec`.

The scope boundary is equally exact: this is a classical inverse on a supplied
raw encoding range for known child and span. It is not an executable parser
for arbitrary files, nor a theorem reconstructing the entire labelled event
history from a canonically merged edge table. `reunion_local_cut_forgotten`
proves why erasing the raw boundary still loses the breakpoint; the new decoder
does not contradict or conceal that information loss.

**Separate claims identified by the original review.**

Full graph measurability, the adaptive conditional mark law, and intrinsic
dated-history factorization were separate pending claims at the original
review checkpoint. The updates below record mathematical acceptance and
subsequently inspected compiler evidence for the dated and measurable-support
constructions. The adaptive-law implementation is outside this bounded review;
its own acceptance record must be used. These claims remain separately named
and all require the root lane's final combined exact-commit verification.

**Initial dated-history review; final support correction and status below.**

Follow-up read-only review of `real/WongMarkedDated.lean` at SHA-256
`271b7b6ed5b5339df9815afe7321af09bc0fe5eea7753df14b9b263e5f568c45`.
The supporting `real/WongMarkedMeasurable.lean` snapshot read for this follow-up
has SHA-256
`830f39d52700f44f21b7464c5262a2d36cf93155cb9832bec42209a1be33a582`.
These were the prototype snapshots reviewed before compilation, not final
compiler or exact-commit evidence. The factorization and failure-handling
analysis below stands. The output-validity claim needed an additional
measurability premise, corrected and discharged in the final update below.

The new `History` stores the stopping index, the explicit stopped result, the
actual recorder state at every capped prefix, and the event-time labels.
`realize` constructs these fields from the same sample. This is a redundant
finite stopped-history representation, since `realize_constant_tail` makes
both displayed paths constant at and beyond the stored horizon. It is not a
claim that an undated graph or a compact canonical edge table determines time.

The original clock counterexample no longer identifies the two outputs: their
`times 1` fields are respectively 1 and 2. The same undated graph can still
occur in both histories, as it should. No source count coordinate, unit-clock
coordinate, or spatial random seed is accessible to `project`; it takes only
`History`. Its count path is `frontierSize (h.states i)`, and its time path is
`h.times`. The equality for counts reuses `recordedCount_eq`, whose proof
checks the generated frontier invariant. The equality for times is now a
lookup of labels actually retained in the output, not a hidden request for
the original input. This closes the precise factorization gap identified
above by enriching the output with the missing data.

The probability construction is also the appropriate one. `historyCode` is
injective and its comap sigma-algebra exposes all stored natural, real, graph,
and sequence coordinates. `measurable_realize` obtains measurability of the
capped states through countable dynamic evaluation of the measurable recorder
prefixes. The separately proved `measurable_project` rules out an unmeasurable
projection being used accidentally. `history_count_time_projection` then
composes the two measurable pushforwards, uses almost-sure equality on `Good`,
and reduces to the checked count/clock marginal. It supports all `n>0`; the
physical correspondence still requires the normalization `theta=2*b/a` with
`a>0` and `b>=0`. The generic factorization theorem deliberately permits other
parameter combinations as a mathematical equality of constructed measures.

A second attempted falsification uses the nonhitting path `K(i)=2` with
`n=2`. Although `firstHit` is totalized to 0 and `states` is the initial
zero-event prefix, `result = stoppedRecord ... = none`. Such a history cannot
satisfy `ValidDated`, which requires `result=some s`. The earlier failure
concern is therefore resolved. `project` remains total and does not suppress
diagnostic prefix values when `result=none`; this is consistent with the
stated almost-sure law theorem, but an interface should inspect `result`
before presenting an arbitrary supplied `History` as a successful run.

The chronology argument uses the correct off-by-one convention. Sample
vertices receive time zero and event vertex `n+j` receives `h.times(j+1)`.
`eventTime_strict_range` proves strict increase only through the finite
pre-absorption event range. `dated_prefix_chronology_bounded` uses the existing
parent-order and vertex-count invariants to put both endpoint event indices
inside that range. Thus completed edges have strictly older parent dates,
without incorrectly asking the terminal constant tail to be strictly
increasing. `realize_validDated` links that chronology to the explicit final
state and final snapshot. In the final compiled `WongMarkedDated`, the endpoint
`law_ae_realize_validDated` asserts almost-sure validity on the INPUT space.
It does not assume that `ValidDated` is measurable on the ambient history
space. The OUTPUT-law theorem is supplied separately by `WongDatedSupport`,
after proving that measurable-support premise, as detailed below.

Two remaining scope distinctions are intentional rather than blockers:

- `History` is an ambient data type, and `ValidDated` is a proved support
  predicate. The latter checks the final state, its dates, the final snapshot,
  and the constant tail; by itself it is not a converse characterization that
  every preceding snapshot was generated by one legal recorder update.
  Actual realization supplies those prefixes by definition and existing
  `prefix_valid_count` supplies their invariants on `Good`.
- This repair establishes a dated marked-history law with an intrinsic
  count-and-time projection. It does not independently supply the conditional
  adaptive mark kernel, an efficient serialization, or a pedigree/species
  interpretation. Those claims retain their separately named proofs.

The remaining measurable-support step and final compiled status are recorded
in the following update. Exact-commit integration remains separate.

**Final support review: compiled input validity, Borel support, and output validity.**

This corrects a specific omission in the prototype review: almost-sure
validity of a realized input was discussed as if transport to the output
measure required no further premise. The predicate on outputs must be
measurable for the chosen `ae_map_iff` route. The final implementation proves
that premise in the existing natural coordinate sigma-algebra; it neither
assumes it nor changes the measurable structure to force it.

The final dated module ends with
`WongMarkedDated.law_ae_realize_validDated`. It states that almost every
input z produces a history satisfying `ValidDated L n (realize ... z)`.
The final output statement is
`WongDatedSupport.historyLaw_ae_validDated`: almost every history under
`historyLaw` satisfies `ValidDated`. Between them sit two explicit support
proofs:

1. `WongMarkedSupport.measurableSet_valid` proves measurability of raw graph
   validity, including exact coverage at every real genomic coordinate.
2. `WongDatedSupport.measurable_validDated` proves measurability of the full
   stored-history support predicate.

The raw-support proof survives a boundary-focused attempted falsification.
An irrational shared endpoint might appear able to hide a gap or duplicate
slot from rational tests. It cannot for this finite family of half-open
intervals: at any x<L, choose y strictly to the right of x, below L and below
every recorded endpoint lying to the right of x. A rational q between x and y
has exactly the same membership in EVERY allocated slot as x. A slot ending
at x is excluded at both points; a slot starting at x is included at both.
Thus any zero-slot or multiple-slot coverage failure also has a rational
witness. Duplicate intervals still have separate slot IDs, so an overlap is
not silently deduplicated. The argument includes all allocated slots,
including active ones, as required by `Valid.coverage`.

Consequently `coverage_iff_rational` replaces the apparent uncountable
coverage condition by a countable formula over natural vertex/slot indices
and rational positions. Every atomic interval comparison is Borel in the
already defined raw-state coordinates. The other validity fields use only
natural-indexed quantification and measurable comparisons. This is an exact
mathematical reduction, not a claim that finitely many observed biological
loci determine coverage or ancestry.

The independent written contribution preserved in
`side-validity/PROOF-HANDOFF.md` gives another valid route: check the finite
set consisting of the genomic lower boundary and all interval endpoints.
It includes coincident endpoints and distinct slot IDs correctly. Its finite
sanity check supports that written lemma but is not a Lean proof. The main
compiled support module uses the rational-witness route above, rather than
claiming to import or mechanize the side script.

For dated support, the existential state in `ValidDated` is fixed uniquely
by `h.result=some s`. `validDated_iff_decoded` removes that existential using
the measurable `decoded` state and a successful-result guard, avoiding an
unjustified uncountable union over states. Equality of raw states and optional
states is measurable through their full injective codes, including countably
many slot/parent coordinates and the event list. Equality of natural-indexed
functions is a countable conjunction. Dynamic evaluation at the natural
horizon or a vertex index is measurable. These facts cover the final snapshot,
counts, constant tails and chronological edge conditions.

The final output proof explicitly supplies
`(measurable_validDated L n).setOf` to `ae_map_iff`, then invokes the compiled
input-space theorem with the same positive-rate assumptions and
`normalizedRatio a b`. This closes the measurable-support gap without a new
probability assumption. It also retains the earlier scope boundary:
`ValidDated` is a support predicate, not a converse characterization of every
legal intermediate transition.

The reviewer read the successful existing module rows and axiom logs and
checked that their source/log hashes match the files below. No compiler was
rerun. The final module evidence is:

| Module | Source SHA-256 | Selected endpoints | Module result |
|---|---|---|---|
| `WongMarkedDated` | `0d89ff9656e5def0b6583b2ddffb71c73206ccb1b56e7b74b133d3219e509974` | 8 | PASS |
| `WongMarkedSupport` | `57d485a53aa9ba32aa98f75c8812b55f1976c142f74fe7624ce819131669a5de` | 3 | PASS |
| `WongDatedSupport` | `162ffdb8b0b3409a9f65ff7b9403a85135be54a2995a7647a3f211c61b8cb993` | 2 | PASS |

Every printed endpoint in these logs uses only `propext`,
`Classical.choice`, and `Quot.sound`. The module results establish the
listed source snapshots. They do not replace the root lane's final combined
exact-commit receipt. No mathematical blocker remains from this bounded
review of factorization, failure handling, or measurable support.

