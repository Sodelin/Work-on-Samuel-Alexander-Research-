# Research follow-up: proof and source packet

This packet records the work following the completed [PR 5 release](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/pull/5). The release and its exact verification evidence remain in [FINAL-RELEASE-RECEIPT.md](FINAL-RELEASE-RECEIPT.md). New local proofs must pass the next aggregate review and CI before they are described as a new public release.

## Start here

| Document | What it explains |
| --- | --- |
| [Full matching height: status update](FULL-HEIGHT-STATUS-UPDATE.md) | The now-unconditional graph height formula and binary-digit evaluator, exact source hashes, and the remaining aggregate verification and library-regularity boundary. |
| [Proposals 3 and 10: source comparison](PROPOSALS3-10-SOURCE-AUDIT.md) | Which ingredients are established slice theory, automata theory and weighted graph methods; the precise remaining contribution and search limits. |
| [Finite-port proof and audit](PROPOSAL3-FINITE-PORT-AUDIT.md) | Exact written encoding/decoding, periodic universality, examples, counterexamples, and the boundary between checked Lean endpoints and the remaining population adapter. |
| [Stateful cellular automaton](PROPOSAL10-STATEFUL-CA-AUDIT.md) | An explicit synthetic three-state rule, its phase certificate, and a strict comparison with every valid static certificate in the specified family. |
| [Directed line graph comparison](LINE-GRAPH-PRIOR-ART-AUDIT.md) | How a classical graph operation gives the two-child, three-root fixed-gender construction; comparison with the pinned manuscript. |
| [Maximal specieslike clusters](MAXIMAL-SPECIESLIKE-SOURCE-AUDIT.md) | Why unrestricted maximality and maximality with reflection differ, with exact source locations and a counterexample. |

## Verification records

- [Finite-phase Lean receipt](FINITE-PHASE-LEAN-RECEIPT.md): arbitrary infinite words in a nonempty finite phase graph with incoming coverage.
- [Finite-state periodicity receipt](FINITE-STATE-PERIODICITY-RECEIPT.md): deterministic finite orbits eventually repeat; determinism is a required proved property when applying this lemma.
- [Stateful CA Lean receipt](STATEFUL-CA-LEAN-RECEIPT.md): complete local rule, actual global evolution, exact static certificate comparison and nonempty finite orbit.
- The finite-port audit includes the frozen `PortDynamics.lean` hash and endpoint map. The graph-to-schedule adapter and canonical converse have a separate implementation owner; the port decoder theorem does not silently assume that adapter has been proved.
- [Pending-document math render check](PENDING-MATH-RENDER-CHECK.json): local MathJax results tied to exact file hashes. These do not assert that unpublished notes have already been visually inspected on GitHub.

The current full-height status is recorded in the new addendum above. Earlier conjectural descriptions remain historical snapshots; they should not be used as the current status of the formula or evaluator. The observation that finite numerical patterns alone do not prove a recurrence remains valid.

## The interpretation to preserve

The strongest value of this packet is its explicit connection between a mathematical claim, its source, its hypotheses and its verification status. A standard method can yield a useful corollary or formalization. Finding its earlier literature strengthens attribution; it does not justify saying the entire original research program has been superseded.

The CA result concerns a synthetic multistate rule and a particular family of speed certificates. A sharper bound for a natural binary or published rule remains a distinct research target. The species result concerns graph-theoretic cluster definitions; it does not certify an empirical biological classification or a theory of psychology.

All new GitHub-facing explanations use protected inline mathematics and fenced math displays. Executable Lean remains Lean code. The reusable delimiter check also corrected two remaining indented display blocks in the finite-edit note without changing their formulas.
