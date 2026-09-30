# Quantitative consequences and a boundary counterexample

Received from the authorized side-chat handoff on 29 September 2026 and
independently checked algebraically by the integration lane. These deductions
use the all-level original-NANUQ theorem and its anchor positivity; they are
not separate historical-priority or statistical-inference claims. The source
chat identifier is `01a0ef7c-7cdc-7f00-a827-8a43b8ae0ffa`.

## 1. An explicit positive support margin

Let a nontrivial circular split have gaps (a,b),(c,d), with b,c on one side.
The distinct quartet set is a nonempty subset of {ab|cd, ad|bc}. Put tau=0
if ad|bc is absent, tau=1 if both topologies occur, and tau=2 if only ad|bc
occurs. Direct substitution gives

    alpha_S(M^{ad}) = alpha_S(M^{bc}) = tau.

The four other anchor pairs among the boundary labels have zero coefficient.
The boundary-quartet lemma makes S displayed exactly when tau>0. Thus, for
positive masses,

    alpha_S(W(m)) >= tau (m(a)m(d) + m(b)m(c)).

For positive integer masses, every displayed nontrivial local split has
alpha>=2, hence split weight alpha/2>=1. A singleton split with neighboring
ports a,d has alpha(M^{ad})=2, yielding the same bound. Global composition
is a sum of these nonnegative lifted split weights, so every positive global
split weight is at least 1. The level-one four-taxon cycle displaying both
planar quartet topologies attains weight 1 on its nontrivial splits.

This strengthens the analytic displayed-implies-positive direction. The
finite zero-for-absence certificate remains necessary in the present proof
of the converse; no four-taxon reduction of all anchor coefficients is claimed.

## 2. The quartet-only residual is a circular pseudometric

For a singleton port b, let a,d be its two circular neighbors. For every other
port t, direct substitution and the two possible planar quartet topologies give

    alpha_b(M^{a,t}) + alpha_b(M^{d,t}) = 2.

Both terms are nonnegative. Together with alpha_b(M^{ad})=2, this implies

    alpha_b(W(m)) >= 2m(a)m(d)
       + 2 min(m(a),m(d)) sum_{t outside {a,b,d}} m(t).

For a port whose attached component is a single global taxon, m(b)=1 and
the total port mass is n. Positive integral masses satisfy
m(a)m(d)>=m(a)+m(d)-1 and min(m(a),m(d))>=1. The displayed bound is therefore
at least 2(n-2). Every global singleton split has such a contribution from
a blob with at least three ports, by the global support proof. Its global
split weight is consequently at least n-2.

Subtracting n-2 from each singleton weight leaves all split weights
nonnegative. Thus the zero-diagonal matrix

    q_N(x,y) = d_N(x,y) - (2n-4), for x != y,

is itself a circular pseudometric in the source class. Its value is exactly
the quartet-sum part of original NANUQ. It need not separate distinct taxa:
in a four-leaf tree, cherry partners have q_N(x,y)=0.

## 3. The optimal strict raw-noise radius is 1/2

In the planar source class each distinct quartet set has one or two
topologies, so every original score rho is 0, 1/2 or 1. The raw distance
is twice a sum of these scores plus the integer baseline 2n-4. Thus every
entry of the original, unnormalized NANUQ matrix is an integer, at every
finite size and level covered by the theorem.

If the entrywise error is strictly less than 1/2, nearest-integer rounding
recovers the exact entire matrix. With the correct circular order supplied,
the exact-support theorem then recovers the displayed-split support.

This universal bound is sharp. In order a,b,c,d, the tree displaying ab|cd
has upper-triangular entries (4,6,6,6,6,4), while the admitted level-one
cycle displaying ab|cd and ad|bc has (5,6,5,5,6,5), in pair order
(ab,ac,ad,bc,bd,cd). Their sup-norm distance is 1, so the same midpoint
lies exactly 1/2 from both, yet their supports differ. Even with the correct
common circular order supplied, no decoder can guarantee support recovery
at closed error radius 1/2, or at any larger strict radius.

The [independent replay and proof](EXTREMALITY-REPLAY.md) verifies both
source models, including the cycle's rooted binary, galled, LSA and
outer-labeled planar conditions. The uniform sharpness witness uses four
taxa; no separate minimax claim for each larger fixed taxon count is made.

The earlier error bound below 1/4 remains valid for direct noisy-coefficient
thresholding: a four-term coefficient changes by less than 1, while true
coefficients are either zero or at least 2, so thresholding at 1 recovers
support. Rounding first improves the admissible error to below 1/2.

These are deterministic guarantees under an exact source-model and error
promise. They provide no sample complexity, estimator analysis or method
for finding a circular order. Distance normalization rescales the radius.

## 4. Outer-labeled planarity cannot simply be removed

Let tree vertices w,v,u,z form the path w-v-u-z. Attach leaf a to u and leaf b
to v. Hybrid h_c has parents w,z and child c; hybrid h_d has parents w,z and
child d. Every internal vertex has degree three. Subdivide u-a by a root,
direct one edge to a, and orient the tree skeleton away from the root before
the edges into the hybrids. This is a binary rooted DAG whose root is LSA.
Each hybrid's two incoming edges plus the skeleton path give a gall without
other hybrid edges. Both hybrids belong to the same blob, so it has level two.

The choices of retained parents for c,d yield:

| Parents | Displayed quartet |
|---|---|
| w,w | ab\|cd |
| w,z | ad\|bc |
| z,w | ac\|bd |
| z,z | ab\|cd |

All three distinct quartet topologies occur. Uniform distinct-topology
averaging gives rho=2/3 for every pair, hence d_N(x,y)=16/3 off diagonal.
That is an equilateral star metric, with no nontrivial metric splits, while
the network displays all three nontrivial quartet splits. Exact support fails.

The network cannot be outer-labeled planar: its three incompatible quartet
splits cannot share a circular order, as required for displayed trees in
such an embedding. This example keeps the other stated structural hypotheses.
It disproves the exact-support generalization after dropping outer-labeled
planarity. It does not disprove circularity: this example's distance is circular.

`nonplanar_support_counterexample.py` independently checks the rooted degree
and DAG conditions, LSA by path domination, the four actual switching trees,
their four-point quartet resolutions, and the exact distance. Its receipt is
`nonplanar-support-counterexample.json`.
