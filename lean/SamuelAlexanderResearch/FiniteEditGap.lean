import SamuelAlexanderResearch.FullHeight

/-! A quantitative matching-height gap away from the dyadic extremal starts. -/
namespace FiniteEditGap

open ThueMorseBits FullHeight

theorem off_extremal_gap (v : Nat) :
    (∃ n, v=3*2^n-1) ∨ FullHeight.height v ≤ v+1 := by
  obtain ⟨h,r,hf,H⟩ := height_closed_form v
  have hq : 0<2^r := Nat.two_pow_pos r
  have hz : (4*h+2)*2^r=2*(v/2+1) := by
    calc
      (4*h+2)*2^r=(2*(2*h+1))*2^r := by congr 1; omega
      _=2*(v/2+1) := by rw [Nat.mul_assoc,←hf]
  by_cases hv : v%2=0
  · rw [if_pos hv] at H
    have he : (4*h+2)*2^r-2=v := by omega
    by_cases hzero : h=0
    · subst h
      by_cases hr : r=1
      · subst r
        apply Or.inl
        refine ⟨0,?_⟩
        simp only [Nat.pow_one,Nat.mul_zero,Nat.zero_add] at he
        simp only [Nat.pow_zero,Nat.mul_one]
        omega
      · apply Or.inr
        simp only [evenValue,t_zero,Bool.false_eq_true,if_false,if_neg hr,Nat.zero_add,t_one,bit,if_true] at H
        simp only [Nat.mul_zero,Nat.zero_add] at he
        omega
    · apply Or.inr
      have hmul := Nat.mul_le_mul_right (2^r) (show 6≤4*h+2 by omega)
      cases ht : t h with
      | true =>
        simp only [evenValue,ht,if_true] at H
        omega
      | false =>
        by_cases hr : r=1
        · subst r
          cases ht' : t (h+1) <;>
            simp only [evenValue,ht,Bool.false_eq_true,if_false,if_pos rfl,bit,ht',if_true,
              Nat.pow_one] at H <;> omega
        · cases ht' : t (h+1) <;>
            simp only [evenValue,ht,Bool.false_eq_true,if_false,if_neg hr,bit,ht',if_true] at H <;>
            omega
  · rw [if_neg hv] at H
    have he : (4*h+2)*2^r-1=v := by omega
    by_cases hzero : h=0
    · subst h
      apply Or.inr
      simp only [oddValue,t_zero,Bool.false_eq_true,if_false] at H
      omega
    · by_cases hone : h=1
      · subst h
        apply Or.inl
        refine ⟨r+1,?_⟩
        rw [Nat.pow_succ]
        simp only [Nat.mul_one] at he
        omega
      · apply Or.inr
        have hmul := Nat.mul_le_mul_right (2^r) (show 10≤4*h+2 by omega)
        cases ht : t h with
        | false =>
          simp only [oddValue,ht,Bool.false_eq_true,if_false] at H
          omega
        | true =>
          cases ht' : t (h+1) with
          | false =>
            simp only [oddValue,ht,ht',Bool.false_eq_true,if_true,if_false] at H
            omega
          | true =>
            cases hs : special h with
            | false =>
              simp only [oddValue,ht,ht',hs,Bool.false_eq_true,if_true,if_false] at H
              omega
            | true =>
              obtain ⟨g,hg,_,_⟩ := special_form h hs
              have hlarge : 5≤h := by omega
              have hmul' := Nat.mul_le_mul_right (2^r) (show 22≤4*h+2 by omega)
              simp only [oddValue,ht,ht',hs,if_true] at H
              omega

end FiniteEditGap
#print axioms FiniteEditGap.off_extremal_gap