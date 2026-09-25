# Proposals 3 and 10: primary-source comparison

**Date:** 25 September 2026. **Mode:** focused rapid evidence map, with direct full-text checks of decisive method claims. This is a bounded literature comparison, not an exhaustive novelty certificate. The mathematical proof packets are [proposal 3](PROPOSAL3-FINITE-PORT-AUDIT.md) and [proposal 10](PROPOSAL10-STATEFUL-CA-AUDIT.md). Their current Lean status must be read separately from the written arguments.

## Findings that change the claims we should make

| Proposed ingredient | Closest verified antecedent | Consequence for the project |
| --- | --- | --- |
| Encode a bounded frontier of a directed acyclic graph using finitely many local pieces | Oliveira's unit slices and regular slice languages, Section 3 | The general representation technique is established. Credit it; specify our infinite fair schedule and population constraints explicitly. |
| Conclude equality of regular infinite-word languages from their ultimately periodic words | Bresolin, Montanari and Puppis, Proposition 3, attributing Büchi and Calbrix et al. | This generic inference is already a theorem. It is not a new unavoidability result by itself. |
| Bound a weighted path by a state potential plus a per-edge constant | Young, Tarjan and Orlin, Section 3 | The certificate algebra is classical. A contribution must concern a faithful model, a new sharp bound, an implementation, or a useful application. |
| Compute the best graph bound through extremal cycle means | Karp; Dasdan and Gupta | This optimization problem and its algorithms already exist. Do not present cycle-mean optimization as invented here. |
| Improve a static CA speed certificate by retaining phase information | The project's synthetic three-state rule supplies an explicit same-rule example | A complete feasibility demonstration is useful. It is not yet a new bound for a published or binary Life-like rule. |

## 1. Finite ports and slice languages

**Primary source:** Mateus de Oliveira Oliveira, [*Canonizable Partial Order Generators and Regular Slice Languages*, arXiv:1009.5341v4](https://arxiv.org/pdf/1009.5341v4), revised 26 June 2012; initially posted in 2010. Section 3, printed pages 5–7, defines numbered incoming/outgoing frontiers, one-vertex unit slices, composition by gluing corresponding frontier edges, and regular languages over finite slice alphabets.

**Explicit mapping, derived here:** one birth update becomes one unit slice. Each unconsumed slot passes directly from its incoming frontier position to its outgoing position. Each consumed slot leads into the new center vertex; each replacement edge leads from that center to the freed outgoing position. Our edge labels and active-source equality partition are additional finite annotations. Gluing reconstructs the finite graph segments.

**Limit of this source match:** the inspected language consists of finite slice strings generating finite DAGs; an infinite language there means infinitely many finite graphs. It does not by itself supply our fair infinite decoder or periodic-tail path lifting theorem. Its partition conventions also address a different purpose. Thus the broad encoding machinery has direct prior art, while those precise infinite population claims still need explicit proof and separate priority review.

An adjacent algorithmic precedent is Bodlaender, Fellows and Thilikos, [*Derivation of algorithms for cutwidth and related graph layout parameters*](https://doi.org/10.1016/j.jcss.2008.10.003), *Journal of Computer and System Sciences* 75(4), 231–244 (2009). Its publisher abstract describes a finite-automata approach to graph layout algorithms, including directed and weighted variants. Only abstract-level inspection is recorded here; it is not used to assert exact subsumption of the population theorem.

## 2. The ultimately periodic word argument is already known

**Primary source:** Davide Bresolin, Angelo Montanari and Gabriele Puppis, [*A Theory of Ultimately Periodic Languages and Automata with an Application to Time Granularity*](https://www.cs.ox.ac.uk/files/3610/ActaInf09.pdf), *Acta Informatica* 46(5), 331–360 (2009). Proposition 3, printed page 7, states both that a nonempty regular infinite-word language contains an ultimately periodic word and that two such languages agree exactly when their ultimately periodic fragments agree. The paper credits Büchi and Calbrix, Nivat and Podelski.

Consequently, **if** the relevant population path language has first been proved regular, Alexander's eventual-periodicity theorem can imply universality through this existing result. The essential unfinished step in the original proposal was proving that regularity and the correspondence with actual graph paths. A finite number of frontier slots alone does not establish it.

Our written proof instead constructs a finite phase quotient from complete periodic updates, proves incoming coverage, applies finite-branching compactness and lifts paths. This avoids importing an entire automata formalization. It does not make the compactness principle new.

## 3. Potentials and cycle means directly precede the stateful method

**Primary source:** Neal E. Young, Robert E. Tarjan and James B. Orlin, [*Faster Parametric Shortest Path and Minimum-Balance Algorithms*, author full text](https://www.cs.ucr.edu/~neal/publication/Tarjan91Faster.pdf), *Networks* 21(2), 205–221 (1991), [DOI:10.1002/net.3230210206](https://doi.org/10.1002/net.3230210206). Section 3, PDF page 8, defines graph potentials, proves the nonnegative reweighting obtained from shortest-path distances when there is no negative cycle, and relates this to minimum cycle means. The 2002 arXiv upload is not the publication date.

For our convention, assign edge cost $`a(e)=c-w(e)`$. Their reweighting condition becomes

```math
w(e)\le c+h(q)-h(q').
```

Thus the proposed certificate is a direct specialization of the established potential method. Summing over a path cancels the intermediate potentials. The general algebra should be attributed, and the task is to establish the correct state graph and useful bound for the actual CA rule.

**Cycle-mean sources:** Richard M. Karp, [*A Characterization of the Minimum Cycle Mean in a Digraph*, Berkeley report ERL-M77/47](https://www2.eecs.berkeley.edu/Pubs/TechRpts/1977/Archive/ERL-m-77-47.pdf) (1977), published in *Discrete Mathematics* 23(3), 309–311 (1978), [DOI:10.1016/0012-365X(78)90011-0](https://doi.org/10.1016/0012-365X(78)90011-0). Maximum means follow by negating weights. Ali Dasdan and Rajesh K. Gupta, [*Faster Maximum and Minimum Mean Cycle Algorithms for System-Performance Analysis*](https://mesl.ucsd.edu/pubs/dasdan-tcad98.pdf) (1998), Theorem 1, explicitly gives the maximum version and algorithmic treatment. These establish the optimization antecedents; the Young–Tarjan–Orlin section is the more direct reference for the potential inequality itself.

## 4. What the synthetic CA establishes

The accompanying proposal 10 proof gives an explicit three-state, quiescent, finite-neighborhood rule. Two live phases alternate, forcing horizontal steps $`+1,-1,+1,-1,\ldots`$. The resulting potential proves horizontal spaceship speed zero. A finite two-cell oscillator demonstrates nonextinct finite-support behavior. An exact checker examines all $`3^6=729`$ neighborhood rows; it reports 135 outputs of one phase and 110 of the other, with both required predecessors and the potential inequality checked in every live row.

The stronger comparison is a mathematical lower bound on **every** valid state-blind, fixed two-label certificate for this same rule: isolated witness rows force $`(1,0)`$ into both step-set convex hulls. The optimum eastward bound obtainable by that static method is therefore 1, while the phase-aware bound is 0. This is a strict information-loss example, not merely a comparison with an arbitrarily weak static certificate.

The phase inequality holds on all chosen parent edges. Ordinary finite branching already supplies a lifeline for this example; prescribed-word unavoidability is not needed to obtain its velocity bound. Alexander's labelled framework remains a compatible setting, but this example does not establish that the stronger unavoidability theorem is essential to the improvement.

**Relevant existing CA bounds:** Nathaniel Johnston's [author proof of B3 spaceship speed limits](https://njohnston.ca/2009/10/spaceship-speed-limits-in-life-like-cellular-automata/) and [B36/S125 paper](https://arxiv.org/abs/1203.1644) supply prior geometric bounds in their stated Life-like families. They must be checked before claiming an improved bound for any rule in those families. Our synthetic multistate example does not improve those results.

## 5. Search record and stopping boundary

The search targeted exact method overlap, not shared biological terminology. Primary full texts were inspected for the decisive slice, automata and graph-potential statements. General web results were used as discovery leads, with secondary records excluded from theorem support. An alphaXiv historical discovery pass supplied adjacent candidates but no independently verified exact replacement theorem.

Representative exact queries executed during this pass:

```text
finite automaton infinite words all states initial incoming transition every letter safety language ultimately periodic words
graph finite cutwidth edge frontier representation finite automata pathwidth periodic graphs
omega regular language determined by ultimately periodic words theorem Buchi primary source
cellular automata spaceship speed bounds weighted graph cycle mean potentials de Bruijn
Karp 1978 minimum cycle mean characterization graph potentials theorem pdf
bounded cutwidth graph representation edge slots finite state periodic infinite graph
"cutwidth" "finite automata" encoding graph
"infinite graphs" "bounded cutwidth" periodic
"sliced" "cutwidth" "automata" graph
"slice automata" "partial orders" Oliveira
"finite automata" "slices" "directed acyclic graphs" width
"A Theory of Ultimately Periodic Languages and Automata" 2009 DOI
"Faster Parametric Shortest Path" "potential" Young Tarjan Orlin pdf
"Canonizable Partial Order Generators and Regular Slice Languages" arxiv.org
"Canonizable Partial Order Generators" pdf Oliveira
"Faster Parametric Shortest Path and Minimum Balance Algorithms" 1991
```

The alphaXiv question was: “Which primary papers already establish finite-state periodic representations of bounded-cutwidth infinite labelled graphs, or state-dependent graph potential certificates for cellular-automaton spaceship speed bounds? Seek exact prior theorems and counterexamples rather than topic similarity.” It used historical prioritization and keywords biologically unavoidable sequences, cellular automata, maximum cycle mean, cutwidth, ultimately periodic words.

**Access and coverage limits:** ranked web/discovery outputs were not exhaustive paginated database searches; total-corpus counts are unavailable. MathSciNet and zbMATH were not searched. A thesis-host PDF retrieval failed; the decisive slice paper was obtained directly from arXiv instead. Broad cutwidth source full text was not obtained. No author contact or claim about what Alexander knows privately was made. Search snippets alone were not accepted as proof of an exact theorem. No global novelty conclusion follows from failure to find an exact population corollary in this pass.

## Recommended attribution and next steps

1. Describe finite ports as a specialized infinite, labelled frontier encoding, with slice theory credited.
2. Describe periodic universality as a proved population corollary using standard finite-state and compactness ideas; keep written proof, Lean verification and priority status separate.
3. Describe the stateful CA example as a strict separation between two certificate classes for one explicit rule, based on classical graph potentials.
4. Preserve the separate research question of a useful improved bound for a natural binary or published rule.
5. Give Alexander the exact assumptions, counterexamples and source mapping. A connection to known mathematics can be valuable even when it removes a broad novelty claim.
