# Bounded all-level source and witness assessment

Date: 2026-09-29. This review follows the user's instruction to prioritize the strongest correct all-level result and stop further raw-graph expansion. It reads the existing adjacent-NANUQ proof and audits; it does not rerun the exhaustive computation or claim a complete Lean theorem.

## Strongest justified statement

Accepting the independently verified exact paired-tip certificate, the written arguments support the following **computer-assisted mathematical theorem**:

> For every finite binary semi-directed phylogenetic LSA network with at least four taxa, if it is galled and outer-labeled planar, its original NANUQ distance is circular decomposable, at every finite reticulation level, including networks with multiple blobs.

The relevant packet is `C:/Users/Owner/Documents/Codex/2026-09-29/vibemathed-biology/adjacent-nanuq/ALL-LEVEL-PROOF.md`, `ALL-LEVEL-STRUCTURAL-AUDIT.md`, `ALL-LEVEL-FINITE-AUDIT.md`, and `ALL-LEVEL-COMPOSITION-AUDIT.md`. The last document explicitly supplies the level-independent transfer from local positively weighted anchor matrices to the full network. The proof draft's initial bloblet-only statement is narrower than the conclusion licensed by that separate composition audit.

This is **circularity**, without an all-level claim that the positive split support is exactly the set of displayed splits. It does not establish all-level canonical reconstruction, statistical consistency, or historical novelty. The full raw-source theorem is not yet kernel checked.

The source match was refreshed against [Holtgrefe et al., Definitions 2.1–2.4 and Section 6](https://link.springer.com/article/10.1007/s11538-025-01549-4). In particular, its binary galled condition is equivalent to each hybrid being an articulation node. [Allman et al., Section 3, paragraph before Figure 4](https://link.springer.com/article/10.1007/s11538-025-01545-8) supplies the required connected root-skeleton observation for galled bloblets without a tree-child assumption. The stronger phylogenetic-skeleton conclusion of their Lemma 3.1 is unnecessary here.

## Critical graph implication and verification boundary

The decisive implication is:

    raw binary galled outer-labeled planar bloblet
      -> plane binary tree with each label occurring once or twice,
         duplicate occurrences adjacent in the cyclic order,
         and exactly the same displayed-quartet support under copy selection.

The face-count proof has the right ingredients: a nontrivial bridgeless subcubic blob has no cut vertex; each hybrid lies on the outer face and exactly one bounded face; the number of bounded faces equals the number of hybrids; every bounded facial cycle meets a hybrid because the root skeleton is a tree. Hence each bounded face contains exactly one hybrid. Opening that face produces a tip-free contour between the two occurrences, preserving their adjacency and the original cyclic taxon order. No reticulation-level bound enters.

I found no new mathematical gap in this written implication on the bounded reread. Its kernel formalization, the rotation-system/face infrastructure, and the precise source suppression/restriction correspondence remain absent. The finite enumeration cannot replace them. Restriction must mean the minimal connecting subtree followed by degree-two suppression, including recursive pruning of unlabeled tips.

For the global extension, actual port maps, positive masses, switching admission, bridge preservation, and triple medians now have substantial Lean foundations. Actual capped local networks, central-star restriction/extension of distinct quartet sets, and the full raw composition identity still need formal assembly.

## Why six has not been reduced to four

A fixed-anchor coefficient is

    alpha = M^(pq)(a,c) + M^(pq)(b,d)
            - M^(pq)(a,d) - M^(pq)(b,c).

Its data can involve six distinct labels `p,q,a,b,c,d`. Keeping those labels preserves all four queried displayed-quartet sets and both boundary gaps. This is the proved six-label reduction. Keeping only four labels need not preserve the coefficient. The fact that a matrix circularity inequality mentions four endpoints does not remove the two additional anchors used to define its entries.

A concrete warning against a quartet-by-quartet shortcut is the following **abstract quartet system**, not a claimed realizable source network. Place six labels in circular order `p,q,a,b,c,d` and prescribe singleton displayed sets:

| Quartet | Prescribed topology | Anchor entry |
|---|---|---:|
| `p,q,a,c` | `pq|ac` | `M(a,c)=0` |
| `p,q,b,d` | `pq|bd` | `M(b,d)=0` |
| `p,q,a,d` | `pd|qa` | `M(a,d)=2` |
| `p,q,b,c` | `pc|qb` | `M(b,c)=2` |

Choose either noncrossing singleton topology for every remaining quartet. Every four-label item is individually a valid circular tree quartet, but the displayed coefficient at gaps `(a,b)` and `(c,d)` is `-4`. The conflict lies in joint realizability, which four-label checks do not certify. The paired-tip tree representation enforces that missing consistency.

This does **not** prove six is a minimal possible witness bound for the source class, and it does not refute a future four-label theorem. It identifies the exact missing theorem: a graph-derived compatibility or monotonicity principle forcing every six-label anchor inequality from four-label information. No such principle is supplied by the current packet. Retaining the already audited six-label certificate is the efficient correct route; its independent exhaustive run was recorded as approximately 18 seconds.

## Parameter-family limitation

`PARAMETER-DOMAIN-AUDIT.md` independently certifies the full local anchor-positivity domain, with anchor-sharing entry fixed at one:

    s = o = 1,   1/2 <= a <= 1,   0 <= c <= a.

This strengthens the original and Modified-NANUQ endpoint statements **for local paired-tip representations and positively weighted bloblet anchor sums**. It is not a necessity theorem for every aggregated unweighted network distance.

The original-NANUQ per-anchor composition identity cannot silently transfer the entire domain to multiple blobs. If an original bridge resolves `pq|xy`, the generalized global anchor entry is `2c`, whereas each local branching-blob anchor entry is zero because one pair collapses. Thus `c>0` needs an additional correction/decomposition. The original score has `c=0`, so this objection does not affect the all-level original-NANUQ theorem above. No generalized multi-blob parameter theorem is endorsed here.

## Raw lane frozen status

The last completed graph modules in this lane are:

- `GraphMedianUnique.lean`: exactly one actual three-port nonleaf blob for every triple of original taxa.
- `GraphPortFibers.lean`: exact original cut-component meaning of every port fiber, and transport of off-direction taxa to one port at a second blob.
- `SourceBlobFacts.lean`: consolidated actual positive port fibers and unique triple medians.
- `GraphQuartetBridge.lean`: two distinct blobs each occupying at least three quartet ports force an original 2+2 bridge, hence one fixed resolution in every actual switching and its exact distinct-topology mean.

All four compiled successfully with Lean 4.33.1 and their printed endpoints use only `propext`, `Classical.choice`, and `Quot.sound`. No active compiler remains in this lane. Earlier `SourceScope.md` records the preceding checkpoint; the four results above are a later delta, not an assertion that its remaining full-source obligations have disappeared.

The other agent reports its generic `AnchorPortPatterns`, `AnchorPortCounts`, `AnchorPortFibers`, and `AnchorPortValues` modules passing. Its raw `GraphQuartetPortCounts.lean` wrapper has unresolved declaration-level classical-instance elaboration errors and must not be treated as a proved endpoint. That failed draft is preserved, with its log, under the explicit instruction to stop expansion.

No frozen packet, earlier proof, external site, or task archive state was changed by this review.
