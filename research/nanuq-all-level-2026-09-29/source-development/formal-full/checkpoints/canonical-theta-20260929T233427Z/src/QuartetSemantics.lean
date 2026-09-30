import Mathlib.Data.Rat.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-!
The source's uniform average is over distinct quartet resolutions, after
restriction to four taxa. It differs in general from averaging switchings.
These definitions do not assume a network decomposition or any positivity.
Raw-network switching/restriction correspondence is a separate obligation.
-/

namespace Nanuq.Quartet

open scoped BigOperators

/-- For an ordered tuple (x,y,z,w), the three binary quartet resolutions. -/
inductive Resolution where
  | xy_zw
  | xz_yw
  | xw_yz
  deriving DecidableEq

/-- Whether the quartet's internal split separates the first two taxa. -/
def separatesFirstPair : Resolution → ℚ
  | .xy_zw => 0
  | .xz_yw => 1
  | .xw_yz => 1

/-- The uniform average of the indicator over a finite SET of resolutions. -/
def distinctMean (s : Finset Resolution) : ℚ :=
  (∑ t ∈ s, separatesFirstPair t) / s.card

/-- Restriction produces one resolution per switching; image deduplicates it. -/
def displayed [Fintype S] (resolve : S → Resolution) : Finset Resolution :=
  Finset.univ.image resolve

def sourceMean [Fintype S] (resolve : S → Resolution) : ℚ :=
  distinctMean (displayed resolve)

def switchingMean [Fintype S] (resolve : S → Resolution) : ℚ :=
  (∑ s, separatesFirstPair (resolve s)) / Fintype.card S

theorem displayed_nonempty [Fintype S] [Nonempty S] (resolve : S → Resolution) :
    (displayed resolve).Nonempty := by
  classical
  exact Finset.Nonempty.image Finset.univ_nonempty resolve

/-- A surjective restriction of choices preserves the DISTINCT quartet set. -/
theorem displayed_comp_surjective [Fintype S] [Fintype T]
    (project : S → T) (hproject : Function.Surjective project)
    (resolve : T → Resolution) :
    displayed (resolve ∘ project) = displayed resolve := by
  classical
  ext q
  simp only [displayed, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨project s, hs⟩
  · rintro ⟨t, ht⟩
    obtain ⟨s, rfl⟩ := hproject t
    exact ⟨s, ht⟩

theorem sourceMean_comp_surjective [Fintype S] [Fintype T]
    (project : S → T) (hproject : Function.Surjective project)
    (resolve : T → Resolution) :
    sourceMean (resolve ∘ project) = sourceMean resolve := by
  unfold sourceMean
  rw [displayed_comp_surjective project hproject]

/-- A constant quartet resolution has no source/switching discrepancy. -/
theorem sourceMean_const [Fintype S] [Nonempty S] (q : Resolution) :
    sourceMean (fun _ : S => q) = separatesFirstPair q := by
  classical
  simp [sourceMean, distinctMean, displayed, Finset.image_const Finset.univ_nonempty]

theorem switchingMean_const [Fintype S] [Nonempty S] (q : Resolution) :
    switchingMean (fun _ : S => q) = separatesFirstPair q := by
  have hn : (Fintype.card S : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [switchingMean, hn]

theorem constant_discrepancy_zero [Fintype S] [Nonempty S] (q : Resolution) :
    sourceMean (fun _ : S => q) - switchingMean (fun _ : S => q) = 0 := by
  rw [sourceMean_const, switchingMean_const, sub_self]

/-- Independent choices away from a blob do not affect the switching average. -/
theorem switchingMean_prod_fst [Fintype S] [Fintype T] [Nonempty S] [Nonempty T]
    (resolve : S → Resolution) :
    switchingMean (fun st : S × T => resolve st.1) = switchingMean resolve := by
  have hs : (Fintype.card S : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have ht : (Fintype.card T : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hsum : (∑ st : S × T, separatesFirstPair (resolve st.1)) =
      (Fintype.card T : ℚ) * ∑ s : S, separatesFirstPair (resolve s) := by
    simpa only [Finset.univ_product_univ, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← Finset.mul_sum] using
      (Finset.sum_product (Finset.univ : Finset S) (Finset.univ : Finset T)
        (fun st => separatesFirstPair (resolve st.1)))
  simp only [switchingMean, hsum, Fintype.card_prod, Nat.cast_mul]
  field_simp

theorem sourceMean_prod_fst [Fintype S] [Fintype T] [Nonempty T]
    (resolve : S → Resolution) :
    sourceMean (fun st : S × T => resolve st.1) = sourceMean resolve := by
  apply sourceMean_comp_surjective Prod.fst
  intro s
  exact ⟨(s, Classical.choice inferInstance), rfl⟩

theorem discrepancy_prod_fst [Fintype S] [Fintype T] [Nonempty S] [Nonempty T]
    (resolve : S → Resolution) :
    sourceMean (fun st : S × T => resolve st.1) -
        switchingMean (fun st : S × T => resolve st.1) =
      sourceMean resolve - switchingMean resolve := by
  rw [sourceMean_prod_fst, switchingMean_prod_fst]

/-- Regression fixture: three switches display one quartet, one displays another. -/
def threeToOne : Fin 4 → Resolution := fun i =>
  if i.val < 3 then .xy_zw else .xz_yw

theorem distinct_average_differs_from_switching_average :
    sourceMean threeToOne = 1 / 2 ∧ switchingMean threeToOne = 1 / 4 := by
  decide +kernel

#print axioms displayed_comp_surjective
#print axioms discrepancy_prod_fst
#print axioms distinct_average_differs_from_switching_average

end Nanuq.Quartet
