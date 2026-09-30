import ThetaFinite

namespace Nanuq.Theta

/-- The concrete finite indexing used by the weighted algebra module. -/
def leafIndex (t : Counts) (i : Fin (circular t).length) : Leaf := leafAt t i.val

/-- Source rho, obtained from the exact twice-rho evaluator. -/
def rhoFin (t : Counts) (a b c d : Fin (circular t).length) : ℚ :=
  rho2 t (leafIndex t a) (leafIndex t b) (leafIndex t c) (leafIndex t d) / 2

theorem circular_length (t : Counts) : (circular t).length = t.total + 2 := by
  simp [circular, Counts.total]
  omega

theorem mem_pairs {n i j : Nat} : (i,j) ∈ pairs n ↔ i < j ∧ j < n := by
  simp only [pairs, List.mem_flatMap, List.mem_range, List.mem_filterMap]
  constructor
  · rintro ⟨a, ha, b, hb, h⟩
    by_cases hab : a < b
    · simp only [if_pos hab, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨hab, hb⟩
    · simp [hab] at h
  · rintro ⟨hij, hjn⟩
    exact ⟨i, lt_trans hij hjn, j, hjn, by simp [hij]⟩

theorem mem_templates_of_bounds (t : Counts) (hlo : 1 ≤ t.total) (hhi : t.total ≤ 6) :
    t ∈ templates := by
  rcases t with ⟨a1,b1,a2,b2⟩
  simp only [Counts.total] at hlo hhi
  simp only [templates, List.mem_flatMap, List.mem_range, List.mem_filterMap]
  refine ⟨a1, by omega, b1, by omega, a2, by omega, b2, by omega, ?_⟩
  simp [Counts.total, hlo, hhi]

theorem bounds_of_mem_templates (t : Counts) (h : t ∈ templates) :
    1 ≤ t.total ∧ t.total ≤ 6 := by
  simp only [templates, List.mem_flatMap, List.mem_range, List.mem_filterMap] at h
  rcases h with ⟨a1, _, b1, _, a2, _, b2, _, h⟩
  split_ifs at h with ht
  · have heq : (⟨a1,b1,a2,b2⟩ : Counts) = t := Option.some.inj h
    simpa [heq] using ht

theorem alpha_nonneg_of_check {t : Counts} (h : checkAnchors t = true)
    {p q i j : Nat} (hpq : p < q) (hq : q < (circular t).length)
    (hij : i < j) (hj : j < (circular t).length) :
    0 ≤ alpha t p q i j := by
  have hpa : (p,q) ∈ pairs (circular t).length := mem_pairs.mpr ⟨hpq,hq⟩
  have hia : (i,j) ∈ pairs (circular t).length := mem_pairs.mpr ⟨hij,hj⟩
  have hp := List.all_eq_true.mp h (p,q) hpa
  exact of_decide_eq_true (List.all_eq_true.mp hp (i,j) hia)

theorem template_anchor_nonneg {t : Counts} (h : checkTemplate t = true)
    {p q i j : Nat} (hpq : p < q) (hq : q < (circular t).length)
    (hij : i < j) (hj : j < (circular t).length) :
    0 ≤ alpha t p q i j := by
  have hparts : checkQuartets t = true ∧ checkAnchors t = true := by simpa [checkTemplate] using h
  exact alpha_nonneg_of_check hparts.2 hpq hq hij hj

set_option maxRecDepth 32768 in
/-- Size of the genuinely generated template list, not a hard-coded bound. -/
theorem templates_length : templates.length = 209 := by decide +kernel

#print axioms mem_templates_of_bounds
#print axioms alpha_nonneg_of_check
#print axioms templates_length
end Nanuq.Theta
