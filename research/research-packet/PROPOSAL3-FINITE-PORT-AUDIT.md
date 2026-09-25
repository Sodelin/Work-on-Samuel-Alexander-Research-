# Proposal 3: exact crossing-port representation and periodic universality

**Status, 25 September 2026.** This note supplies a complete written construction and proof for the mathematical target of proposal 3: an exact finite-port representation of critical tails, its converse decoding, and universality under an eventually periodic complete schedule. The new `PortDynamics.lean` and `FinitePhasePaths.lean` now certify the concrete decoder lifecycle, exact decoder inverse, degree and crossing-edge bijections, fair periodic carryover clearance, and a strictly increasing path for every infinite word. Construction of the canonical encoder from `InfiniteLabeledPopulation` and the converse eventual-periodicity theorem remain written arguments awaiting Lean formalization. Explicit binary width-three and width-four examples are also included. Literature attribution and priority review are being handled separately by the coordinating task; no priority claim is made here. Sections 8–9 give the precise current verification boundary.

## 1. Starting hypotheses and the existing checked input

Let the finite label alphabet be $`A=\{0,\ldots,k-1\}`$, with $`k\ge1`$. Consider the existing simple labelled population on natural-number birth indices. Every edge goes from a smaller index to a larger one. Every nonroot has a parent edge of each label, roots are finite in number, and every vertex has at most $`k`$ children.

The existing `InfiniteConservation.eventual_structure` proves that some cut $`N`$ has both of the following properties:

1. Every vertex $`n\ge N`$ has exactly $`k`$ parents and exactly $`k`$ children, and is not a root.
2. Every cut before a birth $`n\ge N`$ has the same finite number $`C`$ of crossing edges.

Here a crossing edge at cut $`n`$ has source $`u<n`$ and target $`v\ge n`$. Exact indegree and label coverage imply that the incoming edges at every tail vertex carry the labels of $`A`$ exactly once. These are actual graph degrees, not stipulated aggregate counts. The bound $`C\le kR`$, where $`R`$ counts all roots, is available from the same module.

The proof below starts with this checked tail structure. It does not assume the desired encoding as an extra property of a population.

## 2. The finite state and complete action

Fix $`C`$ named slots $`I=\{0,\ldots,C-1\}`$. Slots never move. Each holds one pending edge token. A token keeps its slot until consumed, and consuming a token frees that slot for a newly created token.

The finite state consists of:

- a label vector $`\ell:I\to A`$;
- an equivalence relation $`\pi`$ on $`I`$, where equivalent slots have the same source vertex.

There are at most $`k^C B_C`$ such states, where $`B_C`$ is the number of partitions of a $`C`$-element set. Absolute source indices are not finite-state data. The decoder keeps them as generated vertex identifiers; the partition is exactly the finite information needed to detect whether two current tokens share a source.

A complete action at birth $`n`$ is a pair $`U_n=(S_n,a_n)`$, where:

- $`S_n\subseteq I`$ contains exactly $`k`$ slots to consume;
- $`a_n:S_n\to A`$ specifies the labels of the new tokens inserted into those same slots.

The consumed slots must belong to distinct blocks of $`\pi`$, and their current labels must run through $`A`$ exactly once. The first condition enforces distinct parents and excludes two edges with the same ordered source-target pair. The second enforces incoming-label coverage. All surviving slots keep their labels and source identities. The new slots receive labels $`a_n`$ and become one new source block, representing vertex $`n`$.

Thus the action alphabet is finite, with at most $`\binom{C}{k}k^k`$ possible actions. The sequence of chosen actions is still arbitrary; a finite alphabet or finite control state does not make that sequence periodic.

For permanent source genders, impose the additional local condition that labels are constant on each source block and every newly created block receives a single label. The same construction and theorem then apply without altering the decoder.

## 3. Encoding an actual graph and decoding its schedule

**Finite boundary data.** Retain the original graph on vertices below $`N`$, and assign its $`C`$ crossing edges to slots. For each initial slot record its original source index below $`N`$ and its label. The full crossing target need not be part of the boundary record: its consumption time in the schedule determines it. The finite prefix and its boundary degrees must satisfy the original population requirements.

**Encoder.** Initially sort the crossing edges lexicographically by source and target, assigning them to increasing slot numbers. At birth $`n`$, consume precisely the slots whose targets are $`n`$. There are exactly $`k`$. Sort the $`k`$ outgoing edges of $`n`$ by target and assign them to the newly freed slots in increasing slot order, recording their labels. The other slots retain their edge tokens. This is a deterministic canonical encoding of the given birth-indexed graph.

**Decoder.** At birth $`n`$, a consumed slot with current source $`u`$ and label $`a`$ emits the edge $`u\to n`$ labelled $`a`$. The decoder then inserts a new token with source $`n`$ and label $`a_n(i)`$ in every freed slot $`i`$. It follows the same operation at every birth.

**Required global condition: fairness.** Every initial or newly created token must eventually be consumed. This is not implied by local legality alone. An unconsumed token would be a promised edge with no target, and the advertised slot count would not equal the graph's actual crossing width. Schedules generated from actual graphs are automatically fair because every edge has a finite target index.

**Proof of exactness.** Induct on the birth index. At each cut the encoder's tokens are exactly the graph's crossing edges, with the same sources, labels and slots. Consumption emits exactly the edges ending at that birth; insertion introduces exactly its outgoing edges. Therefore decoding the encoded graph recovers every edge and label, including the finite boundary. For a legal fair schedule, decoding produces exactly $`k`$ distinct outgoing edges at each generated vertex, exactly one incoming edge of each label at every tail vertex, strictly increasing endpoints, and exactly $`C`$ crossing edges at every tail cut.

**What “reversible” means here.** Decoding is a left inverse of the canonical graph encoder. Arbitrarily named valid schedules can encode the same graph. A bijection is obtained by restricting to canonical schedules, or by considering graphs with their slot assignment as additional data. Claiming uniqueness for unrestricted schedules would be incorrect.

## 4. A precise periodicity theorem

**Hypothesis.** For some $`M\ge N`$ and integer $`p\ge1`$, the complete action schedule satisfies

```math
S_{n+p}=S_n,\qquad a_{n+p}=a_n\quad(n\ge M),
```

with the equality of label assignments understood on the identical selected subsets. The schedule is legal and fair as defined above. This is equality of actual named-slot operations, not just equality of counts, anonymous shapes, or source partitions. There is no unrecorded survivor permutation.

**Conclusion.** Every infinite word in $`A^{\mathbb N}`$ is realized by an infinite directed path. More strongly, every such word is realized starting at one of the fixed vertices

```math
M,M+1,\ldots,M+p-1.
```

Different words may require different starts in this finite block.

### Proof A: fairness bounds edge lifetimes

Each slot must occur in at least one of $`S_M,\ldots,S_{M+p-1}`$. Otherwise periodicity would keep it unselected forever, contradicting fairness of its current token.

For $`n\ge M`$ and $`i\in S_n`$, let

```math
\delta_n(i)=\min\{r\ge1:i\in S_{n+r}\}.
```

Then $`1\le\delta_n(i)\le p`$, and periodicity gives $`\delta_{n+p}(i)=\delta_n(i)`$. The token born in slot $`i`$ at birth $`n`$ becomes exactly the edge

```math
n\longrightarrow n+\delta_n(i)
\quad\text{with label }a_n(i).
```

Local simplicity ensures that two tokens born at the same source cannot be consumed together later, so their targets are distinct. The whole outgoing labelled edge list at $`n+p`$ is the list at $`n`$ translated by $`p`$. All tokens present before the periodic part have been consumed by cut $`M+p`$. Thus every incoming edge at a birth $`v\ge M+p`$ comes from a source at least $`M`$.

### Proof B: the finite quotient retains all incoming labels

Make a finite directed labelled multigraph with phases $`0,\ldots,p-1`$. At phase $`r`$, use the outgoing edge list at source $`M+r`$; an edge of displacement $`\delta`$ leads to phase $`r+\delta\pmod p`$. Keep its positive displacement as a tag, so quotient loops and parallel phase edges lose no lifting information.

Every phase has an incoming edge of every label. To see this, select an actual vertex of that phase at least $`M+p`$. Its required incoming edges have sources in the periodic tail, and their phase representatives are precisely quotient edges.

For any finite word, choose any terminal phase and work backwards through the required labels. An incoming edge of each needed label always exists. Hence there is a quotient path spelling that finite word, although its starting phase can depend on the word.

Fix an infinite word. Form the finitely branching tree of matching quotient paths with a superroot over the finitely many starting phases. Every depth is nonempty by the previous paragraph. Konig's lemma supplies one infinite matching quotient path.

Finally, start at the representative $`M+r`$ of its initial phase and add each quotient edge's positive displacement. Translation-periodicity ensures that every lifted edge exists with its recorded label. The lifted indices strictly increase and remain in the periodic tail. This proves the theorem.

The proof does not use Alexander's positive theorem, complementation of omega-regular languages, or the density of eventually periodic words. The finite quotient and its explicitly proved lifting property are sufficient.

## 5. Converse and the scope of the result

**Converse theorem for these critical tails.** If the tail's full labelled adjacency is eventually invariant under translation by a positive period, its canonical slot encoding is eventually periodic.

**Proof.** Finite outdegree at one representative of each phase supplies a uniform maximum edge displacement $`B`$ throughout a sufficiently late tail. Discard the finite carryover from earlier sources. At a cut, record for each slot its source age, residual target distance and label, together with the birth phase. Source ages are between $`1`$ and $`B`$, and residual target distances between $`0`$ and $`B-1`$. This is a finite state. Consumption, decrementing surviving distances, and refilling free slots by increasing outgoing target are deterministic functions of that state and phase. A deterministic evolution in a finite state space is eventually periodic. Its emitted complete actions therefore are eventually periodic. The period can be larger than the graph's translation period.

Consequently the exact encoding identifies eventually periodic full schedules with eventually translation-periodic labelled tails. It does not assert that every critical population has either property.

This periodicity is relative to the chosen natural-number birth enumeration and the stated canonical slot convention. It is not asserted to persist under every other admissible re-enumeration. The universality conclusion concerns the underlying labelled paths and therefore does not depend on how those paths are named.

The universality proof extends beyond critical degree: any forward graph with a finite periodic list of positive labelled offsets at each phase, and late incoming coverage of every label, admits the same finite-quotient argument. Critical conservation is what supplies the finite-port representation for the present populations.

## 6. Binary width-three and width-four examples

The following are direct worked constructions, not extra source theorems. All edges are directed forward. Give vertex $`n`$ the permanent gender $`g(n)`$, inherited by all its outgoing edges.

| Crossing width on the tail | Incoming-parent offsets | Roots and retained edges | Gender function | Canonical consumed-slot cycle |
| --- | --- | --- | --- | --- |
| $`3`$ | $`1,2`$ | Roots $`0,1`$; retain offsets only for targets at least $`2`$ | $`g(n)=n\bmod2`$ | $`\{0,1\},\{0,2\}`$, beginning at birth $`2`$ |
| $`4`$ | $`1,3`$ | Roots $`0,1,2`$; retain offsets only for targets at least $`3`$ | $`g(n)=\lfloor n/2\rfloor\bmod2`$ | $`\{0,2\},\{0,1\},\{0,3\}`$, beginning at birth $`3`$ |

In the first example, the two parents have opposite parities. In the second their indices differ by two, so their genders also differ. Thus each nonroot has both required parent genders. Every late vertex has two children, and the finite prefix respects the cap. Crossing widths are respectively $`1+2=3`$ and $`1+3=4`$.

For width three the initial slots contain edges $`(0,2),(1,2),(1,3)`$. For width four they contain $`(0,3),(1,4),(2,3),(2,5)`$. Applying the canonical consume/refill rule gives the displayed cycles. New tokens all receive $`g(n)`$. The complete action periods are therefore two and twelve, respectively. Both examples realize every infinite binary word by the theorem. The width-four example is not a cap-two avoider and does not settle the open threshold question.

A separate in-memory finite replay checked the declared slots, distinct selected source identities, both incoming genders, unchanged crossing count, and the claimed full-action period for 60 births in each example. This is a check on the worked examples' indexing, not certification of the general encoding or infinite-word theorem.

## 7. Counterexamples to weaker arguments

**Periodic topology and counts do not suffice.** The existing target-dependent graph `BinaryAvoidance.Edge s` has the same unlabelled offsets $`+1,+2`$ on its tail, fixed crossing width three, and one incoming edge of each label at every nonroot. Its canonical slot-consumption pattern and source-partition evolution are periodic independently of the target. Nevertheless, for a non-eventually-periodic target $`s`$, the checked avoidance theorem says that this graph avoids $`s`$. The missing information is the full sequence of assigned labels.

**The all-start infinite-word language need not be closed.** Every finite word occurs somewhere in any eligible population: the vertices at root-distance at most a fixed number form a finite set, so choose a vertex outside that set and backtrack the required parent labels. Yet the preceding avoiding population omits its target infinite word. Finite words realized at successively later starts do not supply a common start for Konig's lemma. The periodic theorem repairs this exact gap by supplying a finite set of starting representatives.

**Every start need not realize every word.** In the width-three permanent-gender example, a fixed start emits only its own gender as the first label. It cannot realize a word beginning with the other gender. The proved quantifiers are “for every word, some start in the fixed finite block,” not “every start realizes every word.”

**Source identifiers cannot be silently discarded.** Consuming two tokens from the same source would create duplicate source-target incidences, even if their labels differed. The partition check prevents this. Absolute identifiers are generated during decoding, while equality of active identifiers is retained in the finite state.

## 8. Logical argument register and remaining work

| Claim | Assumptions | Argument | Verification/provenance status |
| --- | --- | --- | --- |
| Every critical population has a constant-width regular tail | Existing simple population axioms at child cap $`k`$ | `InfiniteConservation.eventual_structure` | Existing Lean endpoint, read as the starting input |
| Exact finite-port representation | That tail; finite prefix and boundary | Induction on consume/refill cuts; distinct source blocks; fair token termination | Decoder lifecycle, exact inverse, degrees as explicit bijections, and slot/crossing-edge bijection now Lean checked; construction of the canonical encoder from `InfiniteLabeledPopulation` remains open in Lean |
| Periodic full schedules imply bounded lifetimes and periodic adjacency | Named immobile slots; eventual full-action period $`p`$; fairness | Every slot selected in a period; first later selection determines its edge | `PortDynamics.next_span_bound`, `bornEdge_shift_iff`, `fair_period_block`, and `fair_period_flush` checked |
| Every infinite word occurs from a fixed finite block | Periodic full schedules; actual consumed-token incoming coverage | Derived quotient incoming edges, finite-rooted Konig argument, positive-displacement lifting | `PortDynamics.periodic_schedule_realizes_strict` checked, using `FinitePhasePaths.realizes_all`; standard compactness ingredients, no priority claim |
| Periodic labelled adjacency implies canonical periodic encoding | Critical tail; finite outdegree; deterministic canonical assignment | Finite state of ages, remaining distances, labels and phase | Complete written converse here; not Lean checked |
| Width-three and width-four periodic examples | Explicit offset and gender formulas | Direct degree, incoming-gender and consume/refill calculations | Worked written examples, not exhaustive classification |

The mathematical conjecture in proposal 3 is resolved under the precise complete-description definition above, and the encoding itself has been supplied as a written construction. The Lean periodic-schedule theorem is also complete. A formal construction of that canonical schedule from the existing population definition, together with the converse eventual-periodicity argument, remains outstanding. Literature novelty remains separately unverified. Nothing here settles cap-two fixed-gender avoidance for nonperiodic schedules or classifies all larger-width tails.

## 9. Formalization handoff, September 25

The new module `lean/SamuelAlexanderResearch/PortDynamics.lean` imports `FinitePhasePaths.lean`. It formalizes concrete stationary slots carrying source identifiers and labels, and updates exactly the slots selected by the schedule. Source identifiers are present in the decoder even though only their equality partition belongs to the proposed finite state description.

### Checked guarantees

| Endpoint | Guarantee |
| --- | --- |
| `run_source_lt`, `decoded_birth_order` | Initial owners preceding the tail imply every decoded edge is strictly forward. |
| `token_origin`, `decoded_born_iff` | A decoded edge between tail births is exactly one token's insertion followed by its next consumption. |
| `decoded_label_unique` | Simple consumption gives a unique label for each source-child pair. |
| `Legal.exact_incoming_parent`, `Legal.incoming_parents_injective` | Every tail birth has precisely one distinct parent for each of the $`k`$ labels. |
| `Legal.exact_outgoing_children`, `Legal.outgoing_children_injective` | Under fairness, the selected input slots provide an explicit bijection between $`\operatorname{Fin}(k)`$ and each tail birth's children. |
| `pending_crosses`, `crossing_from_slot`, `crossing_slots_injective` | Under fairness and simplicity, current slots are an explicit bijective representation of the decoded edges crossing the current cut. |
| `fair_period_block`, `fair_period_flush` | In the periodic tail every slot is consumed in each period, so all tokens carried into a period are replaced during it. |
| `phase_incoming` | The finite quotient's incoming-label property is derived from actual incoming token coverage and full schedule periodicity. It is not a premise. |
| `lift_phase_path` | Quotient edges retain positive displacements and lift to actual birth indices and labels. |
| `periodic_schedule_realizes_strict`, `Legal.periodic_realizes` | Every infinite label word has a strictly increasing decoded path starting in the same fixed block of $`p`$ births. |

**Strengthening found during formalization.** The language theorem itself does not require global fairness. A slot that is actually consumed at a sufficiently late periodic birth was also consumed during the preceding period. Such slots provide all the quotient edges needed for the proof; permanently inactive slots are irrelevant to the path language. Fairness is still essential to interpret every outstanding slot as an actual crossing edge and to recover the exact outgoing degree and width. The Lean theorem separates these uses.

### Exact population adapter still required

For a critical `PopulationCounting.InfiniteLabeledPopulation k k`, the intended remaining adapter must choose a tail birth `base`, a width `C`, a schedule `S : Schedule C (Fin k)`, and `initial : Fin C → Token (Fin k)`, and prove:

1. `Legal S base initial`.
2. `Fair S`.
3. For every child at or after `base`, original adjacency with label `a.val` is equivalent to `DecodedEdge S base initial u v a`.
4. The schedule is the specified canonical sorted refill rule, and `C` is the actual conserved crossing count.

The source population uses `Option Nat` labels. Since the eventual indegree is exactly $`k`$ and it already has a parent of every label below $`k`$, the adapter must also derive the absence of additional labels on edges targeting the tail, rather than assuming the original type was `Fin k`. Neither this conversion nor enumeration of all crossing edges is hidden in `PortDynamics`.

The converse also remains a separate Lean task. Its deterministic finite state may have a transient before entering a cycle: sorted refilling can forget the consumed token-to-slot association. No invertibility or permutation claim is required in the written argument.

### Compilation receipt

The module was compiled in the existing Lean project with the installed toolchain, exit code zero and no warnings:

```powershell
$env:ELAN_HOME='C:/Users/Owner/.elan'
lake env lean -o .lake/build/lib/lean/SamuelAlexanderResearch/PortDynamics.olean lean/SamuelAlexanderResearch/PortDynamics.lean
```

The source SHA-256 at handoff is `445C6AC224B99C66199A157B8895161892954D1584053D2D3440B6F7E4FECD7D`. Ten central endpoint axiom reports contain exactly `propext`, `Classical.choice`, and `Quot.sound`. There are no `sorry` terms or declared axioms. This is a local module compilation receipt; repository-wide integration and publication are owned by the integration task.
