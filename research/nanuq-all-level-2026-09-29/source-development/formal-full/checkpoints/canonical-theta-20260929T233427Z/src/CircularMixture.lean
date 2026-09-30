import CircularBasis

/-! Exact support of a finite mixture, allowing different local contributions
to lift to the SAME global circular split. No cancellation is possible when
the contribution weights are nonnegative. -/
namespace Nanuq.Reconstruction

open scoped BigOperators
open Nanuq.Weighted

variable {n : Nat} {I : Type*} [Fintype I]

def indexedSplitMixture (left right : I → Fin n) (weight : I → ℚ) : Matrix n :=
  fun x y => ∑ k, weight k * gapSplit (left k) (right k) x y

theorem alpha_indexedSplitMixture (left right : I → Fin n) (weight : I → ℚ)
    (horder : ∀ k, left k < right k) (i j : Fin n) (hij : i < j) :
    circularAlpha (indexedSplitMixture left right weight) i j =
      2 * ∑ k, if left k = i ∧ right k = j then weight k else 0 := by
  have hexpand : circularAlpha (indexedSplitMixture left right weight) i j =
      ∑ k, weight k * circularAlpha (gapSplit (left k) (right k)) i j := by
    simp only [circularAlpha, indexedSplitMixture, mul_add, mul_sub,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hexpand, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [alpha_gapSplit _ _ _ _ (horder k) hij]
  by_cases h : left k = i ∧ right k = j
  · simp [h.1, h.2, mul_comm]
  · have hn : ¬ (i = left k ∧ j = right k) := by
      rintro ⟨hi, hj⟩
      exact h ⟨hi.symm, hj.symm⟩
    simp [h, hn]

theorem indexedSplitMixture_alpha_nonneg (left right : I → Fin n) (weight : I → ℚ)
    (horder : ∀ k, left k < right k) (hw : ∀ k, 0 ≤ weight k)
    (i j : Fin n) (hij : i < j) :
    0 ≤ circularAlpha (indexedSplitMixture left right weight) i j := by
  rw [alpha_indexedSplitMixture left right weight horder i j hij]
  apply mul_nonneg (by decide)
  apply Finset.sum_nonneg
  intro k _
  split_ifs
  · exact hw k
  · exact le_refl 0

/-- The support is exactly the union of the positive local contributions,
even when several contributions have identical global boundary gaps. -/
theorem indexedSplitMixture_support (left right : I → Fin n) (weight : I → ℚ)
    (horder : ∀ k, left k < right k) (hw : ∀ k, 0 ≤ weight k)
    (i j : Fin n) (hij : i < j) :
    0 < circularAlpha (indexedSplitMixture left right weight) i j ↔
      ∃ k, left k = i ∧ right k = j ∧ 0 < weight k := by
  rw [alpha_indexedSplitMixture left right weight horder i j hij,
    mul_pos_iff_of_pos_left (by decide : (0 : ℚ) < 2)]
  constructor
  · intro hpos
    by_contra! hnone
    have hnonpos : (∑ k, if left k = i ∧ right k = j then weight k else 0) ≤ 0 := by
      apply Finset.sum_nonpos
      intro k _
      split_ifs with h
      · exact hnone k h.1 h.2
      · exact le_refl 0
    exact (not_lt_of_ge hnonpos) hpos
  · rintro ⟨k, hleft, hright, hpos⟩
    have hterm : 0 < (if left k = i ∧ right k = j then weight k else 0) := by
      simpa [hleft, hright] using hpos
    apply lt_of_lt_of_le hterm
    apply Finset.single_le_sum (f := fun l : I => if left l = i ∧ right l = j then weight l else 0)
      (s := Finset.univ) (a := k)
    · intro l _
      split_ifs
      · exact hw l
      · exact le_refl 0
    · exact Finset.mem_univ k

/-- Pulling back a local interval split gives the global interval split when
the taxon-to-port map has exactly the specified interval preimage. Proving
these interval preimages from a planar embedding is a graph obligation. -/
theorem gapSplit_pullback {m : Nat} (project : Fin n → Fin m)
    (i j : Fin m) (a b : Fin n) (hij : i < j) (hab : a < b)
    (hinterval : ∀ x, inArc i j (project x) ↔ inArc a b x) (x y : Fin n) :
    gapSplit i j (project x) (project y) = gapSplit a b x y := by
  rw [gapSplit_eq_separation _ _ _ _ hij, gapSplit_eq_separation _ _ _ _ hab]
  simp only [hinterval]

#print axioms indexedSplitMixture_alpha_nonneg
#print axioms indexedSplitMixture_support
#print axioms gapSplit_pullback

end Nanuq.Reconstruction
