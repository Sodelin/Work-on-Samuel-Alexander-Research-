# Independent finite audit of the proposed exact-support certificate

**Verdict: pass.** In every saved adjacent-copy system on 3 through 6 labels, absence of the boundary quartet forces every original NANUQ anchor coefficient at that nonadjacent gap pair to be zero. The designated boundary anchor is strictly positive whenever that quartet is present. The pendant-boundary formula also passes in every case.

No tree enumeration was performed. No prior script or receipt was changed. The independent checker is [independent_support_check.py](independent_support_check.py), and its separate exact receipt is [independent-support-check.json](independent-support-check.json).

## Statement checked

Take nonadjacent circular gaps `(a,b)` and `(c,d)`, in that cyclic order, so their four labels are distinct. For each anchor pair `{p,q}`, use the original NANUQ collapsed entries

- `E_pq(x,y)=0` when `x=y` or `{x,y}={p,q}`;
- `E_pq(x,y)=1` when the queried pair shares exactly one anchor;
- `E_pq(x,y)=2 rho(x,y;p,q)` for four distinct labels.

Here the original quartet scores `(cherry, separated, adjacent, opposite)` are `(0,1,1/2,1)`. Define the raw anchor coefficient

`alpha_pq = E_pq(a,c) + E_pq(b,d) - E_pq(a,d) - E_pq(b,c)`.

The checker tests the following three claims using exact fractions:

1. If `bc|ad` is absent from the displayed quartet system, then `alpha_pq=0` for **every** anchor pair, including anchors that overlap the boundary labels.
2. For the boundary anchor `{a,d}`, `alpha_ad=2-2 rho(b,c;a,d)`, and this is positive if and only if `bc|ad` is present.
3. For adjacent gaps oriented so that `b=c`, the anchor `{a,d}` gives `alpha_ad=2`.

The cyclic wraparound cases are included. Display of the requested pair split is tested against the quartet's unordered bipartition, so the check does not incorrectly assume the boundary quartet always uses one fixed bit in the packed representation.

## Exact results

| Labels | Systems | Nonadjacent system/gap cases | Boundary absent | Boundary present | All-anchor zero checks when absent | Pendant checks |
|---:|---:|---:|---:|---:|---:|---:|
| 3 | 1 | 0 | 0 | 0 | 0 | 3 |
| 4 | 3 | 6 | 2 | 4 | 12 | 12 |
| 5 | 16 | 80 | 30 | 50 | 300 | 80 |
| 6 | 102 | 918 | 396 | 522 | 5,940 | 612 |
| Total | 122 | 1,004 | 428 | 576 | 6,252 | 707 |

All 6,252 coefficients tested under absence were exactly zero. The designated boundary-anchor identity was checked in all 1,004 nonadjacent cases. Its value was 0 in the 428 absent cases, 1 in 442 present cases, and 2 in 134 present cases. Every pendant check gave exactly 2. No negative or nonzero-when-absent witness was found.

The run took 0.110 seconds. The input was the previously independently verified system collection in `independent-all-level-check.json`, SHA-256 `e2bd96517422aaa6841fc6b9cc879e8b0a6eaef7ca92fc9904125158195628ed`. The support verifier's SHA-256 is `0d21826e5c5d2dee2215c654ba236d76fa7aba4eb0fc867d09373b0074842d79`.

## Boundary-anchor identities

For four distinct boundary labels, substituting anchors `{a,d}` gives

`E_ad(a,c)=1`, `E_ad(b,d)=1`, `E_ad(a,d)=0`, and `E_ad(b,c)=2 rho(b,c;a,d)`.

This proves the claimed identity directly. In the noncrossing quartet systems under consideration:

- If only `bc|ad` occurs, `{b,c}` is a cherry, so `rho=0` and `alpha_ad=2`.
- If both noncrossing resolutions occur, `b,c` are adjacent in the induced cycle, so `rho=1/2` and `alpha_ad=1`.
- If `bc|ad` is absent, the other resolution separates `b,c`, so `rho=1` and `alpha_ad=0`.

For a pendant boundary, `b=c`, and the same anchor has the first two entries equal to 1 and the last two equal to 0. Its coefficient is therefore 2, independently of the quartet system.

The difficult finite implication is the vanishing of **all other anchors** when the boundary quartet is absent. That is the exhaustive 6,252-case certificate above, rather than an inference from the selected-anchor formula.

## Consequence and remaining structural boundary

Combined with the preceding finite proof of nonnegative original NANUQ anchor coefficients, this establishes the following statement on the checked representation: a sum over all anchor coefficients with strictly positive weights is zero at a nonadjacent gap pair exactly when the boundary quartet is absent. When it is present, the designated anchor contributes positively and all others are nonnegative. Pendant coefficients are positive by the same argument. A positive normalization of the summed coefficient leaves its zero/positive status unchanged.

If an extension permits some anchor weights to vanish, positivity needs a positive-weight witnessing anchor; the present conclusion includes the original sum with unit anchor weights.

The audit does not itself identify a boundary quartet with a displayed split in the external source-network class. Extending the finite zero certificate to larger representations uses the separate restriction argument, and interpreting this as exact source-network split support uses the separately assigned boundary-quartet lifting and distance-decomposition results. Those structural implications must remain explicit. No Modified NANUQ support claim or claim for arbitrary parameter-domain scores is made here.
