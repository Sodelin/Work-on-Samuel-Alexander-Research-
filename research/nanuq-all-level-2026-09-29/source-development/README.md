# NANUQ composition: computer-assisted proof package

Research date: 29 September 2026. This packet develops the first target selected in the broader field review. It is separate from the frozen Alexander embedding/ordinal packet and its Lean manifest. No submission or publication has been made from this chat.

## Result and certification boundary

The written argument establishes the conjectured extension of Holtgrefe et al.'s NANUQ distance theorem from bloblets to networks with multiple blobs, using an exact finite computation for one local lemma. The statement retains the source's restrictions: binary semi-directed LSA networks, at least four taxa, outer-labeled planar, galled, and level at most two. The conclusion is circular decomposability **and exact support equal to the splits of the displayed trees**.

This is a **computer-assisted mathematical argument**. The complete network theorem is not Lean formalized. Four supporting finite-combination lemmas have been kernel checked in Lean; their hypotheses explicitly assume the nonnegative component coefficients, and they do not certify graph admission or the exhaustive enumeration. Historical priority and external peer review are separate from the checks in this packet.

The source is [Holtgrefe et al., Theorem 4.7 and Section 6](https://doi.org/10.1007/s11538-025-01549-4). Its [January 2026 correction](https://doi.org/10.1007/s11538-025-01564-5) restores a figure without changing the result. The conjecture and source correspondence were checked in the prior literature pass. No statistical-consistency theorem or new biological identifiability claim follows automatically from this combinatorial result.

## The mechanism

The complete [composition proof](ordinal/COMPOSITION-PROOF.md) supplies an exact identity, rather than an inequality:

\[
d_N(x,y)=\sum_B W_{L_B}(m_B)(\pi_B(x),\pi_B(y)).
\]

Here each blob is replaced locally by a network whose leaves represent its attached components. A port's mass is the number of original taxa in that component. The sum includes ordinary trivalent vertices between blobs. Two-port blobs contribute zero; three-port blobs contribute positive star metrics.

The weighted local matrix is quadratic in the port masses. It decomposes as

\[
W_L(m)=\sum_{\{p,q\}}m_pm_q M_L^{pq}.
\]

Each two-anchor matrix depends only on distinct displayed quartet topologies. For strictly positive masses, nonnegative anchor coefficients preserve the exact zero/positive pattern of the unit-mass coefficients. The already established bloblet theorem identifies that pattern with the displayed split set.

The local finite reduction is the decisive step. One circular coefficient of one anchor matrix uses at most six named leaves. Deleting other ordinary arm leaves from a canonical theta bloblet, while retaining both hybrid leaves, preserves every quartet needed for that coefficient. Therefore all possible violations reduce to a finite list with at most six ordinary arm leaves, or at most eight leaves total. This is why the finite check covers arbitrary bloblet size; the argument is not an inference from a sample of small networks.

The global proof first decomposes the switching-weighted tree metric, then adds the exact correction to uniform-distinct-quartet averages. That correction is zero for a quartet resolved by a 2+2 cut edge, and otherwise belongs to its unique central blob. The lifted nonnegative split decompositions share one circular order. The written support argument proves both directions: every positive local split extends to a displayed global split, and every displayed global split receives a positive local contribution.

## Verification evidence

| Check | Result | Evidence |
|---|---|---|
| Parent finite template sweep | All 209 theta templates with 1–6 ordinary arm leaves; 100,823 anchor coefficients; none negative. Includes the four three-leaf residual cases. | [Exact implementation](exact_networks.py), [receipt](six-witness-search.json) |
| Independent source implementation | All 205 templates with 2–6 ordinary arm leaves; 100,787 coefficients; none negative. Small retained sets can be padded with an existing fourth leaf. | [Checker](source/anchor_audit.py), [receipt](source/anchor-audit.json) |
| Independent audit implementation | All 209 templates; 100,823 coefficients; none negative; nonuniform-mass expansion also checked. | [Checker](audit/independent_anchor_check.py), [receipt](audit/independent-anchor-check.json) |
| Additional whole-network controls | 20 networks, up to 12 leaves and 6 hybrids; exact global/local identity and support passed. Includes two- and three-blob constructions. | [Control script](composition_controls.py), [receipt](composition-controls.json) |
| Direct network restriction comparison | 324 quartet restrictions built from up-down paths agreed with restriction of the displayed global trees. | [Control receipt](composition-controls.json) |
| Six-leaf source fixture | Independent implementations agree on all 15 distances and all 90 quartet-pair rho values. | [Readable fixture](source/six-leaf-fixture.md), [source audit](source/source-audit.md) |
| Pendant-cluster identity | 45 exact comparisons passed, including a nonzero within-cluster contribution. | [Cluster check](source/cluster-bridge-check.json) |
| Lean supporting algebra | Four theorem endpoints compiled with exit code 0; reported axioms only `propext`, `Classical.choice`, `Quot.sound`. | [Lean source](formal/NanuqPositiveCombination.lean), [compiler log](formal/NanuqPositiveCombination.log) |

The independent quartet evaluators use graph distances and the four-point criterion. The parent uses edge splits from displayed trees. The source fixture distinguishes the intended metric from its switching-weighted counterpart: one entry is 14 under NANUQ and 13 under switching weights. This catches an easy but consequential definition error.

The parent additionally checks connectivity, binary degrees, a rooted acyclic partner, the LSA condition, blob levels, hybrid articulation, and a planar rotation system with all taxa on one face for its constructed controls. These finite admission checks complement the structural argument; they do not replace it for arbitrary networks.

## Reproduction

The Python programs use the standard library only. From this directory:

```text
python exact_networks.py --max-arm 6 --max-total-arm 6 --output six-witness-search.json
python source/anchor_audit.py
python audit/independent_anchor_check.py
python composition_controls.py
```

The parent receipt must have `completed_template_sweep: true`, `template_count: 209`, `anchor_status: PASS`, and `anchor_coefficient_checks: 100823`. A unit-metric status by itself is not the anchor certificate. The independent reports provide separate counts and histograms.

The local [Lean check script](formal/Check.ps1) uses the existing pinned Lean 4.33.1 toolchain and cached Mathlib dependencies. It downloads nothing. Its four endpoints verify linearity, nonnegativity, a positive-coefficient criterion and support invariance for positive finite combinations. Their mathematical role is described in the source header.

## Review and remaining work

The [initial source audit](source/source-audit.md) checks the theta model, finite reduction and exact source metric. The [final source review](source/FINAL-SOURCE-REVIEW.md) supplies full local-admissibility and theta-classification arguments and records a PASS verdict. The [combined mathematical review](audit/COMBINED-REVIEW.md) checks the full composition and support argument together with the finite certificate. These are independent agent reviews within this research session, not external peer review. The optional [interval supplement](ordinal/ANCHOR-INTERVAL-SUPPLEMENT.md) proposes a human structural replacement for the finite enumeration; its theta application is not needed for the present computer-assisted argument and is not being claimed as verified.

The next substantial verification step is full formalization of the graph decomposition, restriction correspondence and finite computation. A later inference algorithm would additionally need an algorithmic construction and explicit conditions under which its quartet inputs can be recovered from data. Those are further tasks, not consequences to silently attach to this theorem.

The original ranking report and first-attack specification remain unchanged as the historical selection record. The new proof package has its own integrity manifest and must not be described as part of the earlier embedding/ordinal Lean certificate.
