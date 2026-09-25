# Finite phase paths: formal statement and scope

`lean/SamuelAlexanderResearch/FinitePhasePaths.lean` proves the finite-state
compactness ingredient used by the periodic-port argument. It imports only
`Std` and was compiled with the repository's pinned Lean 4.33.1.

## Exact endpoint

Let $`p>0`$, let $`A`$ be any label type, and let
$`E:\operatorname{Fin}(p)\times\operatorname{Fin}(p)\times A\to\operatorname{Prop}`$
be a labelled edge relation. Assume every phase has an incoming edge of every
label:

```math
\forall v\in\operatorname{Fin}(p)\;\forall a\in A\;
\exists u\in\operatorname{Fin}(p),\ E(u,v,a).
```

Then `FinitePhasePaths.realizes_all` proves

```math
\forall s:\mathbb N\to A\;\exists f:\mathbb N\to\operatorname{Fin}(p)\;
\forall n\in\mathbb N,\ E(f(n),f(n+1),s(n)).
```

The initial phase may depend on the word. Loops are permitted. An outgoing
edge of every label at every phase is **not** assumed. For example, one phase
can emit only one label and another phase only a different label, while both
phases have both incoming labels. Claiming every word from every fixed phase
would fail in that example.

## Proof and verification boundary

`backward_word` constructs every finite word by choosing incoming edges.
`good_start` uses the finite number of phases to find a start with arbitrarily
long matching paths. `good_successor` preserves this property for a suitable
next phase. `infinite_path_from_good` recursively chooses those successors.
These are proved internally; no compactness or universality axiom is supplied.

The printed axiom report for `realizes_all` contains only `propext`,
`Classical.choice`, and `Quot.sound`. The module contains no `sorry` or new
axiom declarations. Compilation establishes this finite-graph theorem.
Application to populations additionally requires an actual quotient
construction, incoming coverage and path lifting; those belong to
`PortDynamics.lean` and must be checked separately.

## Attribution

The compactness argument is standard mathematics. The related regular-language
principle is recorded in Bresolin, Montanari and Puppis,
[*A Theory of Ultimately Periodic Languages and Automata with an Application
to Time Granularity*](https://www.cs.ox.ac.uk/files/3610/ActaInf09.pdf),
Proposition 3, with attribution there to Büchi and Calbrix et al.
This module does not claim a new general automata theorem.
