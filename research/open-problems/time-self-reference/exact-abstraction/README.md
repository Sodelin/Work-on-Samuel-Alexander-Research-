# Exact deterministic abstraction and a changing rule bit

**Verified:** one Lean 4.33.1 module, eight audited endpoints, two kernel-checked finite trajectories, and two matching executable evaluations. The final compiler run has exit 0 with no warnings or errors. All audited axioms are among `propext`, `Classical.choice`, and `Quot.sound`; several finite-example endpoints use no axioms.

## The exact criterion

Let F : A -> X -> X be a deterministic update controlled by a, and let c : X -> Z be a surjective observation. Then

```text
there exists Fbar : A -> Z -> Z with c(F(a,x)) = Fbar(a,c(x)) for all a,x
    iff
for all a,x,y, c(x)=c(y) implies c(F(a,x))=c(F(a,y)).
```

A fibre of c consists of all concrete states sharing one observation. The criterion says each controlled update must send such states to states sharing a next observation. Necessity follows by applying the same abstract update to equal observations. Sufficiency chooses one representative for each observed state; fibre compatibility makes the resulting update independent of that choice. Surjectivity also makes the abstract update unique on all of Z.

The controlled-trajectory theorem is proved by induction on the number of updates. It preserves every finite trajectory under the identical supplied control sequence. The abstraction does not automatically transfer a policy whose controls depend on hidden state.

This is the standard quotient/congruence factorization criterion. No novelty claim is made.

## Executable two-bit witness

The joint state is (x,r), where x is the visible result and r selects which constant-output rule acts next. The fixed joint update is

```text
F(x,r) = (r, not r),       c(x,r) = x.
```

The internal rule changes on each step. Its update mechanism and the two-bit state space are fixed.

| Joint state | Current observation | Next joint state | Next observation |
|---|---|---|---|
| (false, false) | false | (false, true) | false |
| (false, true) | false | (true, false) | true |

Thus no autonomous deterministic g : Bool -> Bool can satisfy c(F(s)) = g(c(s)) for every joint state s. The map c is well-defined; the obstruction concerns an exact next-state update using its output alone. The proof uses the generic criterion.

The joint update satisfies F(F(F(s)))=F(s), and it has no fixed point. Consequently, every trajectory is periodic from step one with **exact period two**. Both of the following five-state trajectories are checked by `decide` and also printed by `#eval`:

```text
(false,false), (false,true), (true,false), (false,true), (true,false)
(false,true),  (true,false), (false,true), (true,false), (false,true)
```

## Relation to the stated research questions

The paper identified by [DOI 10.1098/rsos.261059](https://doi.org/10.1098/rsos.261059) asks on p. 11 about projecting away the process aspect of generating a result; section 6, starting p. 15, asks about formalisms for systems that change their own rules. Section 7, starting p. 23, revisits representation and remaining modeling gaps.

This module supplies a bounded mathematical interpretation: ask whether a chosen observation supports exact deterministic dynamics across every concrete state in the model. It gives a necessary-and-sufficient test for that interpretation and an explicit failure caused by discarded rule information.

The witness works within a fixed finite metamodel. It makes no claim that arbitrary self-modification, changing languages or semantics, environmental openness, biological self-reference, or unbounded novelty can always be reduced to such a model. It is not a solution to the paper's whole open question. Approximate models, history-augmented observations, and stochastic abstractions require their own contracts.

## Source and verification

Source sidecar: `doc-8b3940d8ac53.pages.jsonl` from the preserved source intake, inspected at PDF pages 11, 15 and 23. Its source PDF SHA-256 is `8b3940d8ac53c7145584c38c1a95a27c87f9c8173323112865c5439862bf43ce`. The sidecar labels its extraction `extracted-unverified`; this lane did not perform a visible-PDF comparison.

- `ExactAbstraction.lean`: definitions, proofs, finite examples, and axiom audit.
- Reproduce from the repository root after the pinned core/real builds with `python checks/audit_research_artifacts.py --output verification/research-artifacts.json`; the CI workflow supplies the dependency preparation.
- `validation.txt`: final clean compiler output and executable trajectories.
- `verification.json`: exact file hashes, source provenance, audited endpoints and assumptions.

Automatic implicit binders are disabled. Only the generic sufficiency construction uses classical choice to choose representatives; the explicit two-bit transition is executable without that choice.

## Concrete merge-history instance

`MergeHistoryProjection.lean` applies this criterion to four-site binary merge forests. Two legal histories have the same unordered current partition and different restored partitions after the same admissible split control. Its separate eight-endpoint receipt and implementation boundaries are recorded in `MERGE-HISTORY.md` and `merge-verification.json`. The two modules together have 16 selected audited endpoints; the portable receipt is `PUBLIC-VERIFICATION.json`.
