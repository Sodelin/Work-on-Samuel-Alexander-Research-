# Independent audit of the per-anchor blob identity

Date: 2026-09-29. Scope: mathematical source/graph audit and inspection of the parent's exact finite control script. This is not a new exhaustive search and not a Lean proof of the identity.

**Verdict:** the proposed identity is mathematically sound with the stated anchor convention, actual bridge-component port maps, and valid local capped-blob quartet restriction. It gives a shorter route to composition. The graph and local restriction steps below still need kernel proofs.

For distinct anchors p,q, let M_N^{pq}(x,y) be zero on the diagonal and when the endpoint pair equals the anchor pair, one when exactly three distinct taxa occur, and 2 rho_N(x,y,p,q) when four distinct taxa occur. Then the proposed identity is

M_N^{pq}(x,y) = sum over nonleaf blobs B with pi_B(p) != pi_B(q) of M_B^{pi_B(p),pi_B(q)}(pi_B(x),pi_B(y)).

The sum must include singleton nonleaf vertices. In particular an ordinary trivalent tree vertex is a contributing blob. Two-port blobs and degree-two root blobs contribute zero. The local pi maps are the actual components incident to the blob, not arbitrary partitions.

## Exhaustive structural cases

1. If x=y, every summand is diagonal and zero. If the endpoint pair equals the anchor pair, each admitted local summand is again the same anchor pair and zero.
2. If exactly three distinct taxa occur, their minimal subtree in the actual blob quotient has a unique median blob. At this blob the three port images are distinct, so its anchor entry is one. At every other blob there are at most two relevant port images: either the anchor images coincide, the endpoint images coincide, or the endpoint pair equals the anchor pair. Every such contribution is zero.
3. If four distinct taxa occur and their minimal blob subtree resolves as pq|xy, the separating bridge forces rho_N(x,y,p,q)=0. At its two branching blobs one pair collapses, so every local contribution is zero.
4. If the minimal blob subtree resolves as px|qy or py|qx, the separating bridge forces rho_N(x,y,p,q)=1. Each of its two branching blobs sees exactly three relevant ports and contributes one; other blobs contribute zero. Both sides of the identity equal two.
5. If the four-taxon blob subtree is a star, there is one central blob with four distinct ports. All other summands vanish. Restricting any global switching to this capped blob gives its local quartet. Conversely every local parent choice extends to a global switching by making arbitrary choices outside the blob. Therefore the *sets of distinct quartet topologies* agree, giving equality of the two rho values and the anchor entries. This argument uses set equality, not multiplicities of switching choices.

These cases are exhaustive after suppressing degree-two vertices in the finite minimal subtree on three or four distinct taxon leaves. Parallel internal edges do not change the bridge quotient argument. Labeled leaves must first be shown to give distinct leaf vertices of that quotient, a remaining convenient formal prerequisite.

## What is already formal and what remains

`GraphBlobs` proves the actual quotient is a tree. `GraphPorts` proves its bridge components contain taxa. `GraphSwitching*` admits actual switchings as finite trees, preserving each original bridge split. `GraphQuartetExistence` and `SourceResolve` prove genuine actual quartet resolution existence and uniqueness. `rawQuartetMean_of_bridge` now proves the exact average in the resolved-bridge cases.

The main unproved ingredients for this identity are the actual port projection for each blob, the three/four-taxon minimal-subtree classification and contribution count, and the central-star local restriction/extension correspondence. Canonical theta coverage and planarity are not needed for this algebraic identity itself; they are needed later to establish local circular nonnegativity for the desired source class. This last separation is an inference from the proof structure, not a new claim attributed to the paper.

## Finite evidence boundary

I read `check_anchor_composition.py`, `anchor-composition-control.json`, and the anchor/quartet evaluator definitions in `exact_networks.py`. The recorded result is 70,913 exact entry equalities over 20 frozen fixtures. The evaluator averages a set of distinct restricted quartet topologies, and its anchor definition matches all structural cases above. It tests all endpoint pairs including diagonal and repeated-anchor cases for each anchor pair.

Those checks are useful controls, not an unbounded proof. The evaluator stores edges as a simple set of endpoint pairs, so this control suite does not independently validate parallel-edge cases. The new Lean raw graph representation retains edge identities and does not share that representation limitation. No frozen file or existing receipt was modified for this audit.
