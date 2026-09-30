import CircularBasis
import Mathlib.Tactic.Linarith

/-!
A circular split is fixed by its two crossed adjacent gaps. This is the
boundary uniqueness needed to lift displayed splits after retaining the four
boundary leaves; it does not assume a graph edge is circular.
-/
namespace Nanuq.Reconstruction

open Nanuq.Weighted
variable {n : Nat}

theorem crossed_gap_is_boundary (k l i : Fin n) (hkl : k < l)
    (hc : ¬ (inArc k l i ↔ inArc k l (cyclicNext i))) :
    i = k ∨ i = l := by
  have hd : cut k i - cut l i ≠ cut k (cyclicNext i) - cut l (cyclicNext i) := by
    rw [cut_sub_eq_arc k l i hkl, cut_sub_eq_arc k l (cyclicNext i) hkl]
    by_cases hi : inArc k l i <;> by_cases hn : inArc k l (cyclicNext i) <;>
      simp_all
  by_contra hnone
  have hik : i ≠ k := fun h => hnone (Or.inl h)
  have hil : i ≠ l := fun h => hnone (Or.inr h)
  have hdiff := cut_boundary_difference k l i
  simp only [if_neg hik, if_neg hil, sub_self] at hdiff
  exact hd (sub_eq_zero.mp hdiff)

theorem two_crossed_gaps_identify_arc (i j k l : Fin n) (hij : i < j) (hkl : k < l)
    (hi : ¬ (inArc k l i ↔ inArc k l (cyclicNext i)))
    (hj : ¬ (inArc k l j ↔ inArc k l (cyclicNext j))) :
    k = i ∧ l = j := by
  have hbi := crossed_gap_is_boundary k l i hkl hi
  have hbj := crossed_gap_is_boundary k l j hkl hj
  rcases hbi with hbi | hbi <;> rcases hbj with hbj | hbj
  · exact False.elim ((ne_of_lt hij) (hbi.trans hbj.symm))
  · exact ⟨hbi.symm, hbj.symm⟩
  · have hcontra : l < k := hbi ▸ hbj ▸ hij
    exact False.elim ((not_lt_of_gt hkl) hcontra)
  · exact False.elim ((ne_of_lt hij) (hbi.trans hbj.symm))

/-- Geometric form: crossing both original adjacent boundary pairs identifies
the exact interval split, even when other leaves are omitted from a witness. -/
theorem gapSplit_identified_by_boundaries (i j k l : Fin n) (hij : i < j) (hkl : k < l)
    (hi : gapSplit k l i (cyclicNext i) = 1)
    (hj : gapSplit k l j (cyclicNext j) = 1) :
    gapSplit k l = gapSplit i j := by
  have hni : ¬ (inArc k l i ↔ inArc k l (cyclicNext i)) := by
    intro h
    rw [gapSplit_eq_separation k l _ _ hkl, if_pos h] at hi
    norm_num at hi
  have hnj : ¬ (inArc k l j ↔ inArc k l (cyclicNext j)) := by
    intro h
    rw [gapSplit_eq_separation k l _ _ hkl, if_pos h] at hj
    norm_num at hj
  obtain ⟨rfl, rfl⟩ := two_crossed_gaps_identify_arc i j k l hij hkl hni hnj
  rfl

#print axioms crossed_gap_is_boundary
#print axioms gapSplit_identified_by_boundaries

end Nanuq.Reconstruction

