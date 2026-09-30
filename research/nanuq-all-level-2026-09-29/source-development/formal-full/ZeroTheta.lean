import ThetaCertificate

/-! The zero-ordinary-leaf case is needed for a total finite compression API.
Only nonnegativity is asserted: the two-leaf zero metric does NOT have the
positive support of its displayed two-leaf tree. -/
namespace Nanuq.Theta

theorem check_zero_template : checkTemplate ⟨0,0,0,0⟩ = true := by
  decide +kernel

theorem counts_eq_zero_of_total_zero (t : Counts) (h : t.total = 0) :
    t = ⟨0,0,0,0⟩ := by
  rcases t with ⟨a,b,c,d⟩
  simp only [Counts.total] at h
  have ha : a = 0 := by omega
  have hb : b = 0 := by omega
  have hc : c = 0 := by omega
  have hd : d = 0 := by omega
  simp [ha,hb,hc,hd]

theorem check_template_upto_six (t : Counts) (hhi : t.total ≤ 6) :
    checkTemplate t = true := by
  by_cases hzero : t.total = 0
  · rw [counts_eq_zero_of_total_zero t hzero]
    exact check_zero_template
  · exact List.all_eq_true.mp all_templates_checked t
      (mem_templates_of_bounds t (by omega) hhi)

theorem anchor_nonnegative_upto_six (t : Counts) (hhi : t.total ≤ 6)
    {p q i j : Nat} (hpq : p < q) (hq : q < (circular t).length)
    (hij : i < j) (hj : j < (circular t).length) :
    0 ≤ alpha t p q i j :=
  template_anchor_nonneg (check_template_upto_six t hhi) hpq hq hij hj

#print axioms check_zero_template
#print axioms anchor_nonnegative_upto_six

end Nanuq.Theta
