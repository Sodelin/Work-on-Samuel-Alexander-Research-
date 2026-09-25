# Independent statement review of the real-number bridge

**Revision note:** the addendum below reviews the subsequently appended real
classification and general degree/root block. It supersedes the original
review's statement that no real binary classification equivalence was packaged.
The earlier source hashes and 15-endpoint count describe the earlier revision;
the addendum records the new source identity and 19-endpoint manifest.

Review date: 25 September 2026 UTC. This is a read-only mathematical and
statement-fidelity review of the owning formalization task's sources. It is
separate from the owner's running compiler and axiom audit. No source files
in that checkout were changed or compiled by this review.

## Disposition

No mathematical defect or conclusion-equivalent premise was found in the
reviewed real-birthdate adapter. The real coefficient endpoints were reviewed
independently against their finite-path and attained-family dependencies.
The limits below should remain attached to the theorem descriptions.

## The literal real-birthdate model

`BinaryRealPopulation V` uses Mathlib's actual `Real` type. Its fields state:

| Field | Mathematical premise |
|---|---|
| `infinite` | No finite list exhausts the arbitrary vertex type $V$. |
| `sublevels` | For every real $r$, only finitely many vertices have birthdate at most $r$. |
| `chronological` | Every directed edge strictly increases the real birthdate. |
| `unique` | An ordered pair of vertices cannot carry two different Boolean labels. |
| `roots` | There are finitely many parentless vertices. |
| `children` | Each vertex has finitely many child vertices, across both labels. |
| `parents` | Every nonroot has an incoming edge of each Boolean label. |

These are the intended binary simple-edge population assumptions. A relational
edge representation permits no multiplicity beyond the label predicate.
Strict chronology rules out loops and cycles. Date ties between vertices are
permitted. Neither countability nor an enumeration nor an unavoidability
conclusion is a field.

`finiteCover_iff_setFinite` identifies the core library's finite-list cover
predicate with Mathlib set finiteness. `BirthOrder.InfiniteVertices` likewise
means that the entire vertex type has no finite cover; the source contains
that equivalence. Thus the finite-list wording does not conceal a different
cardinality assumption.

## How enumeration and transport are obtained

The enumeration is actually constructed. In `BirthOrder.exists_least`, take
any member of a nonempty set, restrict to the finite birthdate sublevel through
that member, and choose a least birthdate in this finite set. Linearity makes
it least in the original set. Repeatedly choose a least unused vertex.

Freshness proves injectivity, and the least-choice property proves
nondecreasing dates. For surjectivity, suppose a vertex $x$ is never chosen.
Every chosen vertex then has birthdate at most that of $x$. More distinct
choices than the finite sublevel's covering-list length give a contradiction.
Choice resolves ties; no computable enumeration is claimed.

Strict chronological edges receive strictly increasing natural indices. The
enumeration's inverse transports finite covers of roots and child sets.
Surjectivity also transfers incoming parents. These arguments supply every
field required by `BinaryNatPopulation p.reindexed`.

`RealBridges.eventuallyPeriodic_realized` invokes the proved positive natural
population theorem and maps the resulting infinite path back to $V$.
Its assumptions are just the real population and eventual periodicity of the
given binary word. The positive theorem is not an input premise.

`finite_real_sublevels_of_strict` is also sound: the non-strict sublevel at
$r$ lies inside the strict sublevel at $r+1$.

## Real-valued sharp coefficients

The original upper endpoint converts the checked natural inequality to
$\ell\le\frac{8}{3}v-\frac{1}{3}$ over the reals. Natural subtraction is removed using
the positive-start hypothesis before casting. Its optimality endpoint uses
the attained dyadic family and the positive real gap $8-3\cdot c$.

The generic helper `coefficient_from_late_witnesses` has an explicit premise
that arbitrarily large starts have actual witnesses with
$8\cdot v \le 3\cdot \ell+B$. That is a legitimate sufficient criterion, not an
unconditional theorem. The concrete finite-edit and phase endpoints derive
this premise internally from their proved path families. They do not ask
the caller to supply the desired optimality claim.

For any real $c<\frac{8}{3}$ and any real additive constant $C$, choose a natural
threshold above $\frac{3C+B}{8-3c}$. A witness beyond it forces
$c\cdot v+C < \ell$. Positivity of the gap, rather than a sign assumption on $c$,
makes this valid for negative coefficients too.

The finite-edit maximum predicate requires an actual `MatchesPrefix`
witness and bounds every other attainable length. It is constructed from
the finite upper bound, with the length-zero path supplying nonemptiness.
The phase maximum is obtained the same way. These are maxima of actual
matching prefixes, not maxima of an unrelated auxiliary trajectory.

The real additive terms are $\frac{8m-1}{3}$ and $\frac{5a-1}{3}$. In the statements
these are real arithmetic, with the natural parameters coerced to reals;
at $m=0$ or $a=0$ they give $-\frac{1}{3}$. They are not truncated natural
subtractions. Positive starts ensure the underlying integer bounds are
cast soundly.

`PhaseShift.shift` and its edge-translation lemmas change both the target
and its associated graph. They retain the destination-at-least-two boundary.
This is distinct from shifting only the requested word while holding the
original graph fixed.

## Scope that must remain explicit

- At the reviewed source state, the real population endpoint proves the
  positive binary theorem. It does not itself package a real-birthdate
  classification equivalence or an arbitrary-finite-alphabet theorem.
- The $\frac{8}{3}$ inequalities measure matching length against natural vertex
  indices, cast to real numbers. They are not bounds against the population's
  physical real birthdates. No quantitative comparison between arbitrary
  timestamps and enumeration indices is proved.
- Coefficient optimality with arbitrary additive constants is checked by
  explicit witness endpoints. This file does not contain a separate theorem
  stated using Mathlib's `Filter.limsup`. The informal limsup interpretation
  requires the supplied upper and arbitrarily late lower witnesses.
- `finite_edit_transport` currently exposes displacement at most $m$.
  Its construction uses $\min(m,\ell)$, but the stronger bound written in our
  audit packet is not a separately exposed conclusion of that endpoint.
- The normalized weighted-mix inclusion is a static module identity:
  choose the same common point from both sets and use $a+b=1$.
  Negative weights are allowed by this valid inclusion. When describing
  a convex mixture, add nonnegativity to that interpretation. Instantiating
  the sets as real convex hulls adds no dynamics or empirical claim.
- New later edits or additional transport endpoints require their own source
  review. This review is not a hosted CI or full-library compilation receipt.

## Reviewed source identities

| Source | SHA-256 |
|---|---|
| `real/RealBridges.lean` | `B4806373114E77C42E8178522B861F0A59D6998E56E26C6AA54039BC3432D6F2` |
| `lean/SamuelAlexanderResearch/BirthOrder.lean` | `9774F28A08F43CCEAB51CC2225B6C572036209C5FE7553F8DE08E834C74B34DB` |
| `lean/SamuelAlexanderResearch/PositiveUnavoidability.lean` | `DD4D241C2752639015FD98B4FB07B044E533B0C21DADB49B6C90EE9EDB925C71` |
| `lean/SamuelAlexanderResearch/FiniteEditStability.lean` | `DBCD4A3EA5F624F807D0FE7998A0D1A2D8BE79BA23AC4946BF05137491F4D998` |
| `lean/SamuelAlexanderResearch/PhaseShift.lean` | `504C71E130463EF9F2DCAC11C77917AA204F42995EE23B722A7DB439C7EA8BE7` |
| `lean/SamuelAlexanderResearch/QuantitativeAvoidance.lean` | `7A24AC5B743A41BB0CAE99FF8E4A095B3767B193D8D4A66D771419723E6FA19A` |
| `lean/SamuelAlexanderResearch/SharpCorollaries.lean` | `22BC1409177624DF85D5FAC7303790BB544B99519A967E4BE7C7E6A7D7E6B2C6` |
| `lean/SamuelAlexanderResearch/SharpThueMorse.lean` | `A2F29F779A19191630D118C5D851FA475E3D0151D55793A0867FEAB50D4BA0EE` |
| `lean/SamuelAlexanderResearch/ThueMorseBound.lean` | `202498AABF53D1BBBDDAC8A02612EF077366FDA34F90E53E59D286380048D0F9` |
| `lean/SamuelAlexanderResearch/BinaryAvoidance.lean` | `CEC0B9D6229A50EC7C4CAE25B121C31B6CAF1AF82AE595BCE0F9A28C01C84F8A` |

The optional project pins Lean `4.33.1` and Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`, and depends on the parent
core package. Its reviewed `RealAudit.lean` lists 15 selected endpoints.
The owner's final compiler output and dependency receipt must be checked
against the submitted revision before publication.

The review was divided into a primary reviewer for the real-population model,
enumeration, and static convex-hull statements, and an independent reviewer
for all real coefficient endpoints and their finite-path dependencies. Both
reported no blocking defect. The latter reviewer rechecked its principal
source hashes at completion; the primary reviewer also rechecked
`RealBridges.lean` before issuing this report.

## Addendum: appended classification and general degree/root block

The subsequent source has SHA-256
`BDF46750B494B863B0536CD131E4837964800144439B5A4E67926566AEC9EE9A`.
Its `PopulationReindex.lean` dependency has the reported frozen SHA-256
`815951D97E90F9DA0AA83CB0ACD8683FFB1AA3460930B7ECA7FB522E986AE666`.
This review covers only the added final block and the relevant transport
definitions. Compilation and the expanded axiom audit remain the owner's
separate verification actions.

### Natural witness lifted to real dates

`binaryRealOfNat` takes an actual `BinaryNatPopulation E` and supplies every
field of `BinaryRealPopulation Nat`. Its birthdate is the natural index cast
to the reals. For any real cutoff $r$, an integer $n > r$ gives a covering
list `List.range n`; thus finite real sublevels are proved, including negative
cutoffs. Chronological order follows by casting the existing strict natural
edge order. Infinitude, uniqueness of labels, finite roots, finite children,
and incoming-label coverage are all transferred from the supplied population.
None is postulated for the constructed witness.

`binary_real_classification` quantifies over vertex types `V : Type` and
populations on them. In the necessary direction, specialize the universal
claim to `Nat` and the actual target-dependent graph `Edge s`, using the
checked `edge_is_binaryNatPopulation s` constructor and the new real adapter.
Its realized path then satisfies `matching_implies_eventuallyPeriodic`.
The sufficient direction invokes the already reviewed positive real theorem.

The result is therefore the full binary classification equivalence for all
small vertex types in the stated real-birthdate model. It contains neither
an assumed avoiding witness nor an assumed classification implication.
The positive theorem remains universe-polymorphic. The equivalence's
explicit `Type` quantifier is accurately documented; it should not be
silently described as a theorem quantified over every universe at once.

### General finite-alphabet degree and root wrappers

`RealLabelledPopulation birth k d` specializes the arbitrary ordered-time
presentation to actual real dates. Its edge is `V -> V -> Option Nat`, with
valid labels restricted to values below $k$; it consequently represents
simple functional labels over a $k$-element alphabet. Roothood means all
incoming edge values are `none`.

The uniform child cap is supplied by covering lists of length at most $d$.
This is a local maximum-child-count premise, not an assumed global counting
inequality. Lists may have duplicates or extra vertices, which cannot make
their length smaller than the number of distinct covered children. The
adapter counts a duplicate-free filtered natural prefix and proves its size
is bounded by the transferred covering list.

`PopulationReindex` constructs the birth-order enumeration, its root
indicator, finite support bounds and actual adjacency counts. The three real
wrappers then provide:

- Impossibility when $d < k$.
- An injective family of $k$ actual parentless vertices.
- A lower bound $k\le\operatorname{length}(\mathrm{roots})$ for every finite list covering all roots.

The injective-family result directly states distinctness; it is stronger than
relying only on a list-length conclusion that might contain duplicates.
The wrappers introduce no new proof premise beyond the population and the
explicit inequality or covering list in their respective statements.
For $k=0$, a valid edge is impossible, making every vertex a root; infinitude
and finite roots therefore make the population assumptions inconsistent.
No nonempty-alphabet positive classification is being smuggled into this case.

The reviewed `RealAudit.lean` now lists 19 endpoints: the original 15 plus
the binary classification and the three general degree/root consequences.
`binaryRealOfNat` is checked as a dependency of the classification endpoint.
These additions do not supply a positive unavoidability theorem for arbitrary
finite alphabets or a quantitative link between indices and real timestamps.

The independent wrapper reviewer also reported a pass, confirming the
two new principal hashes above. Its additional inspected dependency hashes
were `E759C8494D27CFC55656F6E902FF094FBD6DD1E33246C8E84D5689EB8A1A3170`
for `GeneralRootObstruction.lean` and
`5545BC9FB9AE97F48CD1075A7DF2E12087FE53AAFD35F5B141CDEA55540AD627`
for `PopulationCounting.lean`. The labels are single-valued on each ordered
vertex pair, but multiple parents may have the same label: exactly $k$
total parents is not an assumption. No connectivity or positive minimum
time gap is assumed.
