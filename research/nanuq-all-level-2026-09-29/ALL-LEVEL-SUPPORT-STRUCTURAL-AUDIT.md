# All-level support: bounded structural audit

Date: 29 September 2026.

**Verdict: accepted.** A nontrivial circular split is displayed exactly when its boundary quartet is displayed. Positivity on displayed local splits follows analytically from the already accepted anchor nonnegativity. The finite zero-for-absence certificate has now passed, as recorded in Section 6. Six-label restriction gives exact local support at arbitrary level, and the original NANUQ composition identity transfers it to exact global displayed-split support, including bridges and chains of two-port blobs.

This note supplies the structural implication and analytic positivity direction, then records the separately completed finite verification. It does not present that verification as a run performed by this structural audit. It changes no previous proof or certificate.

## 1. Boundary-quartet criterion

Let N have at least four taxa and a circular order C shared by every displayed tree. Let (a,b) and (c,d) be two nonadjacent boundary gaps of C; thus a,b,c,d are four distinct taxa, in that cyclic order. Set

    S = {b,...,c} | {d,...,a}.

Then

    S is a split of some displayed tree of N
      if and only if
    the quartet bc|ad is displayed by N.

For the source semi-directed networks, a quartet displayed by the induced quarnet extends to a displayed tree on all taxa. This is the support implication in the multiplicity identity in the proof of Holtgrefe et al., Lemma 3.2. Proposition 2.9 gives the common circular order for displayed-tree splits in an outer-labeled planar network. Both statements are in [the source article](https://link.springer.com/article/10.1007/s11538-025-01549-4) and do not require level two.

**Forward direction.** A displayed tree containing S restricts on {a,b,c,d} to bc|ad.

**Reverse direction.** Choose a full displayed tree T whose restriction is bc|ad. The central edge of that restricted quartet comes from a nonempty path in T. Any edge e on that path separates b,c from a,d. The split of T induced by e is circular in C. Since a and b are consecutive and lie on opposite sides, the gap (a,b) must be one of its two circular boundaries. The same reasoning makes (c,d) its other boundary. A nonempty circular split has exactly those two boundary gaps, so its split is S. Hence T displays S.

There is no unaccounted placement of intermediate taxa: those placements are forced by the two adjacent gaps. Without the adjacency of each named boundary pair, the quartet would not determine the full split. The criterion does not apply literally to adjacent gaps, which define a trivial split and do not give four distinct quartet labels.

## 2. Displayed local splits have positive coefficients analytically

Let L be a local bloblet with port set P, |P|>=3, in the already audited all-level class. Fix its circular order. Assume the accepted anchor result: every circular coefficient of each two-anchor matrix M^(pq) is nonnegative. For positive masses m,

    W_L(m) = sum_{{p,q} subset P} m(p)m(q) M^(pq).

Use the coefficient convention

    alpha(d) = d(a,c)+d(b,d)-d(a,d)-d(b,c),

with split weight alpha/2.

### Nontrivial displayed split

Suppose S has the four boundary taxa from Section 1 and is displayed. Choose anchors {a,d}. Directly from the anchor definition,

    alpha(M^(ad)) = 1+1-0-2 rho_bc({a,b,c,d})
                  = 2 - 2 rho_bc({a,b,c,d}).

If s is the number of distinct displayed quartet topologies on these four ports, exactly one of them is bc|ad. Therefore rho_bc=(s-1)/s and

    alpha(M^(ad)) = 2/s > 0.

For the planar class s is one or two, so the coefficient is respectively two or one. This computation uses the uniform average over distinct topologies, not switching multiplicities.

All other anchor coefficients are nonnegative. Consequently

    alpha(W_L(m)) >= m(a)m(d) * 2/s > 0.

### Trivial displayed split

For the split {b}|P-minus-{b}, let a,d be the two neighbors of b in the circular order. They are distinct because |P|>=3. Its two gaps are (a,b) and (b,d). With anchors {a,d},

    alpha(M^(ad)) = M(a,b)+M(b,d)-M(a,d)-M(b,b) = 2.

Thus alpha(W_L(m)) >= 2m(a)m(d)>0. Every such trivial split is displayed by every local tree.

These arguments establish strict positivity on every displayed local split without a further finite positivity test. Two-port local matrices are excluded from this claim: their W is zero. Three-port local matrices have the positive star weights already verified in the composition audit.

## 3. Exact finite obligation and its transfer

For a local split S that is not displayed, Section 1 says its boundary quartet bc|ad is absent. Such a split is necessarily nontrivial.

For each anchor pair {p,q}, retain the at-most-six labels

    Y = {a,b,c,d,p,q}

and all of their tip occurrences in the paired-tip representation. Take the connecting subtree and suppress degree-two vertices. The structural audit proves that this preserves the boundary gaps, all quartet sets used by the anchor coefficient, and the absence of bc|ad. The retained instance has four, five, or six labels and belongs to the already enumerated representation domain.

The new finite obligation is precisely:

    For every enumerated representation system, every pair of
    nonadjacent boundary gaps, and every anchor pair,
    absence of the boundary quartet implies alpha(M^(pq)) = 0.

The exact test has passed as recorded in Section 6. The assertion therefore transfers to every original local bloblet at every level. Thus alpha(W_L(m))=0 on every absent local split. Combined with Section 2, this gives

    support(W_L(m)) = union of splits of the displayed local trees,

for every positive mass function and every local bloblet with at least three ports. The finite-verification lane supplies the computation; the preceding argument supplies its transfer to the source-network class.

## 4. Exact local support implies exact global support

Assume the exact local support statement just described. Let N be a finite binary semi-directed LSA, outer-labeled planar, galled network on at least four taxa. Use the original NANUQ composition identity accepted in `ALL-LEVEL-COMPOSITION-AUDIT.md`:

    d_N(x,y) = sum_B W_L_B(m_B)(pi_B(x),pi_B(y)).

All masses are positive. Include singleton trivalent blobs. Local splits lift to circular splits in one fixed global order. Two-port blobs contribute zero.

### Every positive lifted local split is globally displayed

Take a split of a local displayed tree in a blob B with at least three ports, and choose a local switching that realizes it. Extend that choice arbitrarily to every other blob; the switching choices are independent. Gluing the local switching trees through the cut edges gives the global displayed tree after pruning and suppression.

The local edge representing the split gives the corresponding global taxon bipartition, replacing each port by its entire taxon component. Positive port masses ensure neither side vanishes. If the local edge is pendant, its lift is the split at that attachment; if it is internal, its lift is the corresponding split through B. Suppression may replace a path by a single edge but preserves the bipartition. Therefore every split receiving positive local weight is globally displayed.

### Every globally displayed split has a positive local source

Choose a global switching tree T displaying a split S, and an edge e inducing it. Since T is a binary tree on at least four leaves, e has an internal degree-three endpoint v. This v is an original tree vertex, because pruning and degree-two suppression create no new branching vertices. Let B be its unique original blob.

Each of the three branches of T at v contains a global taxon. Every branch exits B through at least one port, and a given port's taxon component is contained wholly in one of those branches. Thus v is also a degree-three branching vertex of the local displayed tree T_B and B has at least three ports.

The local edge leaving v in the direction of e separates exactly the port groups whose taxa lie on that side of the global edge. Its lifted split is S. If the global edge represents a suppressed path crossing one or more two-port blobs, the same argument applies at its branching endpoint v: those intermediate zero-contribution blobs do not remove the split provided by B. This also covers original bridges and pendant taxon splits.

By the assumed exact local support theorem, this local split has a strictly positive weight in W_L_B(m_B). It therefore gives a positive contribution to the global split S.

### No cancellation

All local coefficients are nonnegative and all lifted splits are circular in the same global order. Contributions to the same global split add; they cannot cancel. The two preceding directions show that their union is exactly the displayed-split system of N. Hence

    support(d_N) = union of splits of all displayed trees of N.

This implication is independent of reticulation level. The two-port exception is handled by the branching endpoint argument, not by falsely asserting positive support for W on two ports.

## 5. Final status

The boundary-quartet equivalence is proved. Strict positivity on displayed local splits is proved analytically from the accepted anchor nonnegativity. The transfer from exact local support to exact global support is proved, with positive masses, bridges, singleton trivalent blobs, and zero two-port blobs all accounted for.

The finite zero-for-absence assertion in Section 3 has now been discharged by the independent certificate inspected in Section 6. No mathematical gap remains in this assigned structural transfer. The conclusion retains the exact computer-assisted verification status of its finite ingredients; this is not a Lean certificate. No generalized parameter-family support claim, canonical-form statement, statistical inference guarantee, or historical-priority claim is made.

Only this file was written. No existing proof, Lean file, Git state, or external site was changed; no new agents or broad searches were used.

## 6. Finite pass received and inspected

After the structural proof was written, the integration lane relayed the finite pass. I then read `ALL-LEVEL-SUPPORT-FINITE-AUDIT.md` and `independent-support-check.json` and verified that the receipt's recorded input and verifier hashes match the files. The test was not rerun in this structural lane.

The exact receipt reports 122 saved systems, 1,004 nonadjacent system/gap cases, and 428 cases with the boundary quartet absent. All 6,252 associated anchor coefficients are zero. The 576 present cases have a positive designated boundary-anchor coefficient, either one or two, and all 707 pendant checks give two. There is no failure witness. This discharges precisely the finite obligation in Section 3; it is not being used to infer the structural lemmas from examples.

The input-system SHA256 is `e2bd96517422aaa6841fc6b9cc879e8b0a6eaef7ca92fc9904125158195628ed`; the support-verifier SHA256 is `0d21826e5c5d2dee2215c654ba236d76fa7aba4eb0fc867d09373b0074842d79`.

Receipt SHA256: `d2611d6fbdbc4f390c3a6f499f8f25b52d03615c6ae08b78871ab2b89e91fec4`.
