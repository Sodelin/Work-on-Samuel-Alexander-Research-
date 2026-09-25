# Generic natural certificates for labelled-path avoidance

25 September 2026. **Lean checked, exit code 0.** This closes the arbitrary-vertex and arbitrary-alphabet restriction for the natural-certificate theorem. It does not formalize the separate ordinal omega, leaf-pruning, or Schmidt-rank claims.

## Statement

Let V be any vertex type, A any label type, E a labelled edge relation, and s a target sequence. A realization is an actual infinite vertex path whose successive edge labels are s(0), s(1), and so on. A reachable state (v,k) is the endpoint and length of some finite matching prefix beginning at phase zero.

Assume each vertex has finitely many children of each fixed label. Then:

```math
\neg\operatorname{Realizes}(E,s)
\quad\Longleftrightarrow\quad
\exists r:R_s\to\mathbb N\;
\forall ((v,k)\to(w,k+1)),\quad r(w,k+1)<r(v,k).
```

The least such rank exists pointwise and is an attained maximum of finite continuation lengths in the reachable-state graph. The formal endpoint states both attainment (`ChainLength` at exactly that rank) and an upper bound for every finite `ChainLength`.

There is no Bool encoding, vertex enumeration, birth-order assumption, root condition, finite-alphabet requirement, or supplied continuation-length bound. The ordinary finite-outdegree condition implies the per-label hypothesis; this implication is also checked. Thus an Alexander population can use this certificate result directly at its existing vertex and label types, through its finite-child axiom. A source representation still needs to instantiate the edge relation faithfully; no chronology conversion is required by this theorem.

## Proof route

1. Concatenate a reaching prefix with an infinite reachable-state chain to recover an actual full realization. Conversely, every realization gives such a state chain.
2. Mathlib's `wellFounded_iff_isEmpty_descending_chain` converts absence of a chain into well-foundedness of reversed state transitions.
3. Well-founded recursion assigns each state the finite supremum of its child ranks plus one, with value zero when there are no children.
4. Finite supremum properties prove strict decrease, pointwise leastness, and attainment by a finite state chain.
5. An infinite realization would force an infinite strictly decreasing sequence of natural ranks, a contradiction.

This is a formalization of a standard argument from well-founded recursion and finite branching. No novelty of the general method is claimed. The representation restriction removed here was a gap in our earlier implementation, not a newly discovered obstruction in Alexander's mathematical model.

## Exact evidence

See [GenericCertificate.lean](GenericCertificate.lean), [compiler output](validation.txt), and [verification.json](verification.json). All eight printed endpoints use only `propext`, `Classical.choice`, and `Quot.sound`, or a subset. The source has no `sorry`, `admit`, or new axiom declaration. Only installed Lean 4.33.1 and the already cached Mathlib dependencies were used. Neither source checkout nor publication stage was edited.

The formal maximum is noncomputable and uses classical choice. This theorem does not provide a decision procedure for arbitrary graph descriptions, derive an empirical species criterion, or distinguish different avoiders by different transfinite ranks.

## Reproduce

In the prepared repository's Mathlib environment, run:

```powershell
lake env lean /absolute/path/to/GenericCertificate.lean
```

The archived run invoked the same installed compiler directly with the cached library directories in `LEAN_PATH`. If later promoted into the repository library, its import and selected endpoint receipt must be added to the relevant ordinary build. This isolated check is separate from the published 405/101 aggregate.
