# Active packet: global parameter-family circularity

Packet ID: `NANUQ-PARAMETER-GLOBAL-01`.
Status: open continuation packet; the existing theorem package is independently
publishable without solving this extension.

## The question

For a finite binary semi-directed LSA, outer-labeled planar, galled network
with arbitrarily many blobs, use the displayed-quartet score rule `(c,s,a,o)`
from [Section 6 of the proof](../nanuq-all-level-2026-09-29/ALL-LEVEL-PROOF.md).
Which points of `s=o=1, 1/2<=a<=1, 0<=c<=a` give a circular decomposable
**unweighted global distance** for every network in this class?

Try first to prove the whole region or produce an exact counterexample to
that statement. If it fails, preserve the counterexample and state the largest
region you actually proved, with the unresolved portion explicit.

## Inputs and facts already available

- [Current proof](../nanuq-all-level-2026-09-29/ALL-LEVEL-PROOF.md): the whole
  region works locally on bloblets; original NANUQ `(0,1,1/2,1)` works globally.
- [Exact parameter inequalities](../nanuq-all-level-2026-09-29/PARAMETER-DOMAIN-AUDIT.md).
- [Original composition identity](../nanuq-all-level-2026-09-29/ALL-LEVEL-COMPOSITION-AUDIT.md).
- [Other lane's assessment](../nanuq-all-level-2026-09-29/source-development/formal-full/SourceAllLevelAssessment.md): the original composition formula cannot simply be reused unchanged when `c>0`.
- External motivation: Holtgrefe et al., [Section 6](https://doi.org/10.1007/s11538-025-01549-4), parameter-family question; Allman et al., [NANUQ+ Definition 3.1](https://doi.org/10.1186/s13015-025-00274-w).

Use uniform distinct displayed quartet topologies. Switching multiplicities
are a different quantity. A negative individual anchor coefficient does not
by itself disprove circularity of their unweighted sum.

## Bound and stopping condition

Spend one focused pass on a decomposition proof and, if tools are available,
one bounded exact search. Before running a search, state its graph family and
maximum size. Do not enumerate arbitrary large networks or rerun the entire
existing Lean development. Stop with a proof, a source-admitted exact
counterexample, or a specific lemma whose truth remains undecided.

Do not start biological estimation, all-level canonical identification,
nonplanar networks, psychology, or an unrelated literature survey in this packet.
Those are separate questions. Do not claim this packet's region is maximal
outside the stated candidate domain without a separate necessity proof.

## Return contract

Record the exact base commit read from main. Return `RESULT.md`,
`EVIDENCE.json`, and any proposed `PARAMETER-GLOBAL.md` proof or check script.
If no execution tools are available, provide the mathematical argument and
mark code/formal verification as not run. Do not edit prior receipts.
The integration owner reviews this contribution before it becomes a new
public theorem or a VibeMathed update.
