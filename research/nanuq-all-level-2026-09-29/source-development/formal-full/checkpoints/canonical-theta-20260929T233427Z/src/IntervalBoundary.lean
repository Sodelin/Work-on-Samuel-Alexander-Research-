import CircularBoundary
import Lean.Elab.Tactic.Omega

/-! An integer interval, or its complement, has exactly the two circular
boundaries that it crosses. Endpoints zero and n are allowed. -/
namespace Nanuq.Reconstruction

open Nanuq.Weighted
variable {n : Nat}

theorem halfOpen_two_crossings (a b : Nat) (hbn : b ≤ n)
    (i j : Fin n) (hij : i < j)
    (hi : ¬ ((a ≤ i.val ∧ i.val < b) ↔
      (a ≤ (cyclicNext i).val ∧ (cyclicNext i).val < b)))
    (hj : ¬ ((a ≤ j.val ∧ j.val < b) ↔
      (a ≤ (cyclicNext j).val ∧ (cyclicNext j).val < b))) :
    (∀ x : Fin n, (a ≤ x.val ∧ x.val < b) ↔ inArc i j x) ∨
      (∀ x : Fin n, (a ≤ x.val ∧ x.val < b) ↔ ¬ inArc i j x) := by
  have hex : ∃ x : Fin n, a ≤ x.val ∧ x.val < b := by
    by_contra! hnone
    have hn (x : Fin n) : ¬ (a ≤ x.val ∧ x.val < b) := by
      intro hx
      exact (not_lt_of_ge (hnone x hx.1)) hx.2
    exact hi (iff_of_false (hn i) (hn (cyclicNext i)))
  have hnall : ∃ x : Fin n, ¬ (a ≤ x.val ∧ x.val < b) := by
    by_contra! hall
    exact hi (iff_of_true (hall i) (hall (cyclicNext i)))
  obtain ⟨u, hu⟩ := hex
  have hab : a < b := by omega
  by_cases ha : a = 0
  · obtain ⟨v, hv⟩ := hnall
    have hbp : 0 < b := by omega
    have hblt : b < n := by omega
    let k : Fin n := ⟨b - 1, by omega⟩
    let l : Fin n := ⟨n - 1, by omega⟩
    have hkl : k < l := by show b - 1 < n - 1; omega
    have hform (x : Fin n) : (a ≤ x.val ∧ x.val < b) ↔ ¬ inArc k l x := by
      simp only [inArc, Fin.lt_def, Fin.le_def, k, l]
      omega
    have hic : ¬ (inArc k l i ↔ inArc k l (cyclicNext i)) := by
      simpa only [hform, not_iff_not] using hi
    have hjc : ¬ (inArc k l j ↔ inArc k l (cyclicNext j)) := by
      simpa only [hform, not_iff_not] using hj
    obtain ⟨hk, hl⟩ := two_crossed_gaps_identify_arc i j k l hij hkl hic hjc
    right
    intro x
    simpa only [hk, hl] using hform x
  · have hap : 0 < a := by omega
    let k : Fin n := ⟨a - 1, by omega⟩
    let l : Fin n := ⟨b - 1, by omega⟩
    have hkl : k < l := by show a - 1 < b - 1; omega
    have hform (x : Fin n) : (a ≤ x.val ∧ x.val < b) ↔ inArc k l x := by
      simp only [inArc, Fin.lt_def, Fin.le_def, k, l]
      omega
    have hic : ¬ (inArc k l i ↔ inArc k l (cyclicNext i)) := by
      simpa only [hform] using hi
    have hjc : ¬ (inArc k l j ↔ inArc k l (cyclicNext j)) := by
      simpa only [hform] using hj
    obtain ⟨hk, hl⟩ := two_crossed_gaps_identify_arc i j k l hij hkl hic hjc
    left
    intro x
    simpa only [hk, hl] using hform x

theorem interval_predicate_two_crossings (P : Fin n → Prop) (a b : Nat) (hbn : b ≤ n)
    (hform : (∀ x, P x ↔ a ≤ x.val ∧ x.val < b) ∨
      (∀ x, P x ↔ ¬ (a ≤ x.val ∧ x.val < b)))
    (i j : Fin n) (hij : i < j)
    (hi : ¬ (P i ↔ P (cyclicNext i))) (hj : ¬ (P j ↔ P (cyclicNext j))) :
    (∀ x, P x ↔ inArc i j x) ∨ (∀ x, P x ↔ ¬ inArc i j x) := by
  rcases hform with hform | hform
  · have hic := hi
    have hjc := hj
    simp only [hform] at hic hjc
    rcases halfOpen_two_crossings a b hbn i j hij hic hjc with h | h
    · exact Or.inl (fun x => (hform x).trans (h x))
    · exact Or.inr (fun x => (hform x).trans (h x))
  · have hic := hi
    have hjc := hj
    simp only [hform, not_iff_not] at hic hjc
    rcases halfOpen_two_crossings a b hbn i j hij hic hjc with h | h
    · right
      intro x
      exact (hform x).trans (not_congr (h x))
    · left
      intro x
      simpa only [not_not] using (hform x).trans (not_congr (h x))

theorem interval_separation_identified (P : Fin n → Prop) [DecidablePred P]
    (a b : Nat) (hbn : b ≤ n)
    (hform : (∀ x, P x ↔ a ≤ x.val ∧ x.val < b) ∨
      (∀ x, P x ↔ ¬ (a ≤ x.val ∧ x.val < b)))
    (i j : Fin n) (hij : i < j)
    (hi : ¬ (P i ↔ P (cyclicNext i))) (hj : ¬ (P j ↔ P (cyclicNext j)))
    (x y : Fin n) :
    (if P x ↔ P y then (0 : ℚ) else 1) = gapSplit i j x y := by
  rw [gapSplit_eq_separation _ _ _ _ hij]
  rcases interval_predicate_two_crossings P a b hbn hform i j hij hi hj with h | h
  · simp only [h]
  · simp only [h, not_iff_not]

#print axioms halfOpen_two_crossings
#print axioms interval_predicate_two_crossings
#print axioms interval_separation_identified

end Nanuq.Reconstruction
