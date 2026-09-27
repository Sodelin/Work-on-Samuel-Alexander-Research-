import WongPedigreeBridge

set_option autoImplicit false

/-!
# IAP transfer with finite ancestry disagreement across an owner projection

This weakens the IAP part of `WongPedigreeBridge.iap_iff`: for each rich-history
member, finitely many ancestry-path answers inside the saturated candidate may
disagree with the pedigree. Their number need not have a common bound, and the
disagreements may occur between different owners. The owner map must still be
onto and have finite fibres.

This is a deduction from Alexander's IAP definition and finite-set calculus,
not a source claim or a biological species classification. It gives no
convexity, connectivity, maximality, or REF conclusion. The error condition
concerns transitive ancestry, not the number of edited immediate-parent edges.
-/

namespace WongPedigreeRobust

open SpeciesBridge WongPedigreeBridge

/-- IAP agrees across an onto finite-fibre owner map if every member's
ancestry row has only finitely many disagreements inside the candidate. -/
theorem iap_iff_of_finite_projection_errors (owner : Nat → Nat) {R E : Graph}
    (onto : Function.Surjective owner) (fibres : FiniteFibres owner) (S : NatSet)
    (errors : ∀ a, Pull owner S a → FiniteSupport
      (fun b => Pull owner S b ∧
        ¬ (Descendant R a b ↔ Descendant E (owner a) (owner b)))) :
    IAP R (Pull owner S) ↔ IAP E S := by
  classical
  have finiteRows (a : Nat) (ha : Pull owner S a) :
      (FiniteSupport (fun b => Pull owner S b ∧ Descendant R a b) ↔
        FiniteSupport (fun v => S v ∧ Descendant E (owner a) v)) ∧
      (FiniteSupport (fun b => Pull owner S b ∧ ¬ Descendant R a b) ↔
        FiniteSupport (fun v => S v ∧ ¬ Descendant E (owner a) v)) := by
    have agree (b : Nat) (notBad : ¬ (Pull owner S b ∧
        ¬ (Descendant R a b ↔ Descendant E (owner a) (owner b))))
        (hb : Pull owner S b) :
        Descendant R a b ↔ Descendant E (owner a) (owner b) := by
      by_contra h
      exact notBad ⟨hb, h⟩
    constructor
    · apply Iff.trans ?_ (finiteSupport_preimage_iff owner onto fibres _)
      apply finiteSupport_iff_off_finite (errors a ha)
      intro b notBad
      change (Pull owner S b ∧ Descendant R a b) ↔
        (Pull owner S b ∧ Descendant E (owner a) (owner b))
      by_cases hb : Pull owner S b
      · exact and_congr Iff.rfl (agree b notBad hb)
      · simp only [hb, false_and]
    · apply Iff.trans ?_ (finiteSupport_preimage_iff owner onto fibres _)
      apply finiteSupport_iff_off_finite (errors a ha)
      intro b notBad
      change (Pull owner S b ∧ ¬ Descendant R a b) ↔
        (Pull owner S b ∧ ¬ Descendant E (owner a) (owner b))
      by_cases hb : Pull owner S b
      · exact and_congr Iff.rfl (not_congr (agree b notBad hb))
      · simp only [hb, false_and]
  constructor
  · intro h v hv
    obtain ⟨a, rfl⟩ := onto v
    rcases h a hv with hd | hn
    · exact Or.inl ((finiteRows a hv).1.mp hd)
    · exact Or.inr ((finiteRows a hv).2.mp hn)
  · intro h a ha
    rcases h (owner a) ha with hd | hn
    · exact Or.inl ((finiteRows a ha).1.mpr hd)
    · exact Or.inr ((finiteRows a ha).2.mpr hn)

end WongPedigreeRobust

#print axioms WongPedigreeRobust.iap_iff_of_finite_projection_errors
