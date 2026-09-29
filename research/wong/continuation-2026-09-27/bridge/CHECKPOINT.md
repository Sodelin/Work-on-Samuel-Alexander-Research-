Bridge checkpoint, 2026-09-27.

Starting commit: `01db8c4cbb82000950ff7d3e7252b5438416c7c3`.
Owned paths: `real/WongPedigreeBridge.lean` and this `bridge/` directory.
The parent lane owns integration, the exact final commit, audit registration,
and the combined verification receipt.

The new Lean source passed the parent's serialized verifier on 2026-09-27:
34 project modules in its import closure passed or were reused only with
matching source/dependency hashes. All 14 printed acceptance endpoints use
only `propext`, `Classical.choice`, and `Quot.sound`; three require no axioms.
Lean is 4.33.1 and mathlib is pinned to
`0df444a360eaa60ab8c11dca51a86af692955474`.

Verified source SHA-256:
`a50265e3c458bac5577116ee8fc30bea5f7b881ebd4216040543ce4adb5f921b`.
Printed-axiom log SHA-256:
`598954f8d3246701da2a5f61d63b309ce6e0c13eb8adec7bba3201310d2c0282`.

The preserved receipt still names the starting HEAD and records an uncommitted
working-tree snapshot. This is a verified source snapshot, not yet the final
integrated exact-commit claim. That remaining check belongs to the parent lane.
`verification/RESULT.json` distinguishes those statuses explicitly.

Verified endpoints:

- `finiteSupport_preimage_iff` and `infiniteSupport_preimage_iff`.
- `iap_iff`: exact IAP transfer under onto finite-fibre owner maps and ancestry
  equivalence away from equal-owner fibres.
- `reflection_iff`, `commonAncestor_descends`, `convex_pullback`, `convex_iff`,
  and `specieslike_descends`.
- `specieslike_iff`, `maximal_saturated_iff`, and `maximalSpecieslike_descends`
  with connected owner fibres.
- `iap_iff_of_finite_ancestry_errors`: robustness to finitely many path-answer
  discrepancies per source member.
- `sound_projection_does_not_determine_iap`: the same infinite rich history
  and identity owner map have two sound biosphere interpretations with
  opposite IAP.
- `no_specieslike_recovery_from_garg_coarsening`: any deterministic summary of
  finite gARG data retains the abstract-completion recovery obstruction.

Not asserted: pedigree maximality implies unrestricted rich-history maximality.
The equivalence is proved only among saturated candidate sets, with a separate
one-way descent theorem from unrestricted rich maximality of a saturated set.

Not proved or claimed: the faithful-owner assumptions hold for sampled ARGs;
an empirical owner assignment; full biological pedigree recovery; any DNA
observation likelihood; statistical non-identifiability in a specified
Wright–Fisher model; a transfer of real birthdates from ARG event times;
biological species classification; a novel theorem of the cited authors.

The first pass found two elaboration errors, both repaired: the REF proof
needed explicit unfolding of `InfiniteSupport`, and the connectivity lift
needed endpoint rewriting before constructing the irreflexivity contradiction.
The failed evidence is retained as `verification/attempt-1.*`; it is not part
of the accepted proof evidence.

Shortest next route: register this successful module/endpoints in the parent's
audit and ledger, then verify the integrated exact commit. The independent
source review is recorded in `SOURCE-REVIEW.md`. For model-dependent inference,
first fix
a pedigree/inheritance/observation class before seeking distribution-level
counterexamples or identifiability proofs.
