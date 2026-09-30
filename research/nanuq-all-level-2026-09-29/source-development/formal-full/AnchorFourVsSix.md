# Four-point tests and six-label anchor tests are different

A fixed full distance matrix is circular decomposable in a fixed order exactly when its adjacent-gap circular coefficients are nonnegative. Each such coefficient reads four entries of that same full matrix. This does not reduce source NANUQ validation to recomputing the metric on four-taxon induced objects: restriction changes the witness sum and the constant term. In general, restricting the full distance matrix and recomputing the four-taxon distance give different matrices.

There is a compact exact obstruction to the generic four-taxon-to-weighted-anchor implication. On circular order 0,1,2,3,4,5, use the following three binary circular trees, specified by one side of each internal split:

- T1: 01, 015, 0125.
- T2: 012, 0123, 0345.
- T3: 0123, 045, 0145.

For each quartet, restrict all three trees, deduplicate the resulting quartet topologies, and average the cherry-separation indicator uniformly over that set. With anchors p=0, q=5, the four relevant values are:

| Endpoints x,y | Distinct quartet topologies | rho(x,y,0,5) | Anchor entry M^(0,5)(x,y) |
| --- | --- | ---: | ---: |
| 1,3 | 01\|35; 13\|05 | 1/2 | 1 |
| 2,4 | 24\|05; 02\|45 | 1/2 | 1 |
| 1,4 | 01\|45 | 1 | 2 |
| 2,3 | 23\|05; 02\|35 | 1/2 | 1 |

Thus the coefficient for boundaries (1,2) and (3,4) is 1+1−2−1 = −1. These are six distinct labels: four boundary labels and two anchors. The attached JSON records a fresh exact integer split-restriction calculation of these four values.

Nevertheless every four-taxon restriction passes circular decomposability. On four taxa, its recomputed NANUQ metric is precisely the average of the ordinary quartet-tree metrics for its distinct displayed quartets. Every such quartet is compatible with the same induced circular order, so that average is circular decomposable. This argument covers every four-taxon restriction without a search.

The negative anchor also gives positive terminal masses with a negative weighted coefficient. Set m0=m5=33 and all other masses to 1. The anchor expansion has one term −33². Each other anchor coefficient is at most 4 because anchor entries lie in [0,2]; there are eight remaining pairs with one heavy mass and six with neither. Hence the weighted coefficient is at most −33²+8·4·33+6·4 = −9.

Scope: this is a compatible circular-tree family, not a supplied realization by an admissible phylogenetic network. It disproves the generic inference from four-taxon validation to weighted anchor positivity. It does not disprove the all-level network conjecture. A valid all-level proof may impose stronger compatibility among quartet sets arising from actual network switchings. The checked theta proof retains six witnesses because that information is actually sufficient; replacing it by four needs such an additional theorem, not the observation that final circularity uses four matrix entries.
