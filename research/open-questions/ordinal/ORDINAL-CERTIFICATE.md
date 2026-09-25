# Ordinal certificates at arbitrary vertex and label types

25 September 2026. **Lean checked, exit code 0.** This is the separate ordinal-valued certificate corollary of the exact reachable-state representation in `GenericCertificate.lean`. It does not change that frozen file.

## Exact statement

For any vertex type V, any label type A, any labelled edge relation E, and any target sequence s:

```math
\neg\operatorname{Realizes}(E,s)
\quad\Longleftrightarrow\quad
\exists r:R_s\to\operatorname{Ord}\;
\forall ((v,k)\to(w,k+1)),\quad r(w,k+1)<r(v,k).
```

Here R_s consists exactly of endpoint/phase pairs reached by a finite matching prefix starting at phase zero. `Realizes` means an actual infinite vertex path matching the target's successive labels. The ordinal values are taken in the universe of the vertex type; the soundness theorem also permits certificates valued in ordinals of any universe.

**No finite-branching hypothesis is needed.** Birth dates, roots, a finite alphabet, natural vertex indexing, and decidability assumptions are also absent. With finite per-label branching, the earlier generic result additionally supplies a least natural-valued certificate and attained finite maxima.

## Proof and meaning

The earlier exact prefix-plus-tail argument gives avoidance iff the reversed reachable-state transition relation is well founded. Mathlib's `Acc.rank` then assigns an ordinal to each reachable state, and `Acc.rank_lt_of_rel` gives strict decrease. Conversely, a decreasing ordinal certificate transports the well-founded ordinal order back to the state relation, excluding an infinite matching path.

This is the classical ordinal characterization of well-founded relations applied to this graph representation. It closes the arbitrary-vertex/alphabet restriction for this precise interpretation of Alexander's [Section 6 characterization question](https://arxiv.org/html/1212.0186v2#S6). It does not claim a newly invented rank method, an executable test for arbitrary graph inputs, or a hierarchy distinguishing different avoiding populations.

The source population axioms are stronger than the assumptions here. Applying this statement requires representing the source's actual labelled edges and target faithfully; no conversion of birth dates or labels is required by the theorem.

## Checked endpoints

1. `GenericOrdinalCertificate.ordinal_certificate_excludes_realization`.
2. `GenericOrdinalCertificate.avoidance_has_ordinal_certificate`.
3. `GenericOrdinalCertificate.avoids_iff_ordinal_certificate`.

All three printed dependency lists contain only `propext`, `Classical.choice`, and `Quot.sound`. See `GenericOrdinalCertificate.lean`, `ordinal-validation.txt`, and `ordinal-verification.json`. The file was checked with the installed Lean 4.33.1 compiler and cached Mathlib. The earlier `GenericCertificate.lean` source hash was checked before building its scratch import artifact and remained unchanged.

## Reproduction and remaining boundary

Build `GenericCertificate.lean` to `GenericCertificate.olean` in a local directory visible in `LEAN_PATH`, then compile `GenericOrdinalCertificate.lean` in the same prepared Mathlib environment. A publication workflow that checks these isolated files must build the former before checking the latter.

This file does not calculate the matching-history root rank, transfinite leaf-pruning stages, or Schmidt rank. Those are distinct statements with separate formalization receipts. It adds no biological identification claim and no empirical validation.
