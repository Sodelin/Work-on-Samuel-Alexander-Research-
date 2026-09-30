# Side-package replay and the sharp raw-noise radius

**Verdict: the single fresh Node replay passes, and the new strict noise radius 1/2 is justified.** Nearest-integer rounding recovers the exact original, unnormalized NANUQ matrix under entrywise error strictly below 1/2. With the correct circular order supplied, the established exact-support theorem then recovers its displayed-split support. The admitted four-taxon tree/cycle pair proves that the bound cannot be enlarged uniformly.

## Fresh replay

The preserved source is [verify_nanuq.js](source-development/extremality-sidechat/verify_nanuq.js). It was run exactly once with `C:\Program Files\nodejs\node.EXE`, returned exit code 0, and completed in 0.719 seconds with empty stderr. Its **entire parsed JSON** equals the supplied [verification-results.json](source-development/extremality-sidechat/verification-results.json), including the finite support and refinement outputs.

The complete fresh stdout, executable/source/result/proof hashes, equality check, and exact endpoint arithmetic are saved in [EXTREMALITY-REPLAY.json](EXTREMALITY-REPLAY.json). The three source files read for this task were unchanged after execution. The source contains no imports, filesystem calls, or network operations; its only output is the JSON written to standard output.

The replay reports 84,076 tree configurations, 2,525,210 complete occurrence selections, 122 quartet/support systems, and 24,667 anchor checks. It has zero negative coefficients, support mismatches, or boundary failures. These are fresh execution results. This task independently audits only the new sharp-noise statement below; it does not independently re-audit every other mathematical assertion included in the side package.

## Integer-lattice recovery

For the admitted planar class, every displayed quartet set is a nonempty subset of the two resolutions compatible with the fixed circular order. Uniform averaging over distinct resolutions therefore gives

`rho in {0, 1/2, 1}`.

For the original raw distance,

`d_N(x,y) = 2 sum_{unordered {z,w} disjoint from {x,y}} rho_xy + 2n - 4`

off the diagonal, while the diagonal is zero. Every term `2 rho` and the baseline are integers, so **every entry of d_N is an integer**, at every admitted finite size and level. This uses the planar source promise and the original score convention; it does not hold for arbitrary four-score parameters or arbitrary distance normalizations.

For an integer k and real z satisfying `|z-k|<1/2`, k is the unique nearest integer to z. Applying this fact to every matrix entry proves

`||Dhat-d_N||_infinity < 1/2  ==>  round(Dhat) = d_N`.

There are no rounding ties under the strict bound. The matrix recovery itself requires no circular order. Recovering exact split support by the coefficient formula then uses the supplied correct order and the already established source-class support theorem.

The verifier's finite rounding examples are supplementary sanity checks. The universal rounding conclusion follows from the analytic argument above, not from sampling finitely many integers or decimal errors.

## Admitted endpoint pair and impossibility at radius 1/2

In the common order `a,b,c,d`, let T display only `ab|cd` and let C display `ab|cd` and `ad|bc`. Their original raw distances are symmetric, have zero diagonal, and have these off-diagonal entries:

| Pair | ab | ac | ad | bc | bd | cd |
|---|---:|---:|---:|---:|---:|---:|
| Tree T | 4 | 6 | 6 | 6 | 6 | 4 |
| Cycle C | 5 | 6 | 5 | 5 | 6 | 5 |
| Common midpoint | 9/2 | 6 | 11/2 | 11/2 | 6 | 9/2 |

Thus `||D_T-D_C||_infinity=1`, and the midpoint is at distance exactly `1/2` from each. At the gaps `(a,b),(c,d)`, the raw circular coefficient

`D(a,c)+D(b,d)-D(a,d)-D(b,c)`

equals 0 for the tree and 2 for the cycle. Their supports differ: the cycle adds the split `ad|bc`. The replay receipt independently checks both matrices, the norm, both midpoint radii, and these two coefficients with exact rational arithmetic.

The same observed midpoint and supplied circular order are compatible with both true supports under an error bound of `<=1/2`. Therefore no decoder can guarantee the correct support for every admitted source at that closed radius. Every larger strict radius also includes this ambiguous midpoint. Together with the rounding result, this establishes **the optimal strict universal radius 1/2**. The witness is four-taxon; this is a uniform result over the source class, not a separate minimax claim for every fixed network or every fixed larger taxon count.

## Cycle admission, checked directly

The construction in [PROOF-REFINEMENTS.md, Section 9](source-development/extremality-sidechat/PROOF-REFINEMENTS.md) is valid. Start with cycle vertices `v_a,v_b,v_c,h_d` in that order, with one pendant taxon at each. Place root r on the b pendant edge. Orient

`r -> b`, `r -> v_b`, `v_b -> v_a`, `v_b -> v_c`,

`v_a -> a`, `v_a -> h_d`, `v_c -> c`, `v_c -> h_d`, `h_d -> d`.

The root has outdegree two; every ordinary internal vertex has indegree one and outdegree two; `h_d` has indegree two and outdegree one. There is one gall, with internally disjoint branches from `v_b` through `v_a` and `v_c` to `h_d`, and one reticulation, so the network is binary, galled, and level 1. All four pendant taxa lie on the outer face. Because b is a separate root child, no vertex below r is an ancestor of all taxa, and r is the least stable ancestor of the complete taxon set. Suppressing the degree-two root in the semidirected representation gives the stated cycle with pendant b.

Keeping the parent edge from `v_a` gives `ad|bc`; keeping the edge from `v_c` gives `ab|cd`. The comparator tree `ab|cd` is also admitted, with a binary root on its internal edge. Both therefore lie in the source class and have the same valid circular order; the ambiguity is not created by an inadmissible graph or an order mismatch.

## Interpretation

The earlier strict `1/4` error bound remains a sufficient guarantee for direct noisy-coefficient thresholding. The stronger strict `1/2` guarantee uses the additional integer-lattice structure to restore the matrix first, and is optimal for uniform exact recovery in the stated raw-distance model.

This is deterministic recovery under a source-matrix and error promise. It supplies no statistical sample complexity, no claim that a particular empirical estimator satisfies that promise, and no order-finding algorithm. A rescaling of the distance rescales the noise radius. No Lean build, register-wide investigation, source edit, Git operation, or publication occurred in this task.
