import ThetaFiniteSoundness
import WeightedCoefficients
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.NormNum

/-! Source evaluator / weighted-anchor correspondence, including taxon indexing. -/
namespace Nanuq.Theta

private theorem arm_map_nodup (k : Fin 4) (l : List Nat) (h : l.Nodup) :
    (l.map (Leaf.arm k)).Nodup := by
  apply h.map
  intro a b hab
  exact (Leaf.arm.inj hab).2

private theorem arm_maps_disjoint (k r : Fin 4) (hkr : k ≠ r) (l s : List Nat) :
    List.Disjoint (l.map (Leaf.arm k)) (s.map (Leaf.arm r)) := by
  rw [List.disjoint_left]
  intro a ha hb
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
  obtain ⟨j, _, heq⟩ := List.mem_map.mp hb
  exact hkr (Leaf.arm.inj heq).1.symm

theorem circular_nodup (t : Counts) : (circular t).Nodup := by
  have ha (k : Fin 4) (r : Nat) : ((List.range r).map (Leaf.arm k)).Nodup :=
    arm_map_nodup k _ (List.nodup_range (n := r))
  have har (k : Fin 4) (r : Nat) :
      ((List.range r).reverse.map (Leaf.arm k)).Nodup :=
    arm_map_nodup k _ (by simpa using (List.nodup_range (n := r)))
  simp only [circular, List.nodup_append, List.nodup_cons, List.nodup_nil,
    List.not_mem_nil, not_false_eq_true, and_true, List.mem_append,
    List.mem_cons, List.mem_map, List.mem_reverse, List.mem_range]
  simp [ha, har, Leaf.arm.injEq, or_imp, forall_and, forall_exists_index, and_imp]

theorem leafIndex_injective (t : Counts) : Function.Injective (leafIndex t) := by
  intro i j hij
  apply Fin.ext
  exact (List.getD_inj i.isLt j.isLt (circular_nodup t)).mp hij


/-- Exact agreement of the executable leaf-based anchor with the finite-taxon
matrix used by weighted NANUQ algebra. -/
theorem weighted_anchor_eq_anchor (t : Counts)
    (p q x y : Fin (circular t).length) :
    Nanuq.Weighted.anchorMatrix (rhoFin t) p q x y =
      anchor t (leafIndex t p) (leafIndex t q) (leafIndex t x) (leafIndex t y) := by
  have heq : ∀ a b, leafIndex t a = leafIndex t b ↔ a = b :=
    fun a b => (leafIndex_injective t).eq_iff
  unfold Nanuq.Weighted.anchorMatrix anchor
  simp only [heq]
  by_cases hxy : x = y
  · simp [hxy]
  · have hboth :
        ((x = p ∨ x = q) ∧ (y = p ∨ y = q)) ↔
        ((x = p ∧ y = q) ∨ (x = q ∧ y = p)) := by
      constructor
      · rintro ⟨hxp | hxq, hyp | hyq⟩
        · exact False.elim (hxy (hxp.trans hyp.symm))
        · exact Or.inl ⟨hxp, hyq⟩
        · exact Or.inr ⟨hxq, hyp⟩
        · exact False.elim (hxy (hxq.trans hyq.symm))
      · rintro (⟨hxp, hyq⟩ | ⟨hxq, hyp⟩)
        · exact ⟨Or.inl hxp, Or.inr hyq⟩
        · exact ⟨Or.inr hxq, Or.inl hyp⟩
    simp only [hxy, if_false, hboth, or_assoc]
    split_ifs <;> simp [rhoFin] <;> ring

/-- The finite certificate evaluates exactly the circular coefficients of the
weighted module's anchor matrix; successor normalization is definitionally equal. -/
theorem weighted_alpha_eq_alpha (t : Counts)
    (p q i j : Fin (circular t).length) :
    Nanuq.Weighted.circularAlpha (Nanuq.Weighted.anchorMatrix (rhoFin t) p q) i j =
      alpha t p.val q.val i.val j.val := by
  simp only [Nanuq.Weighted.circularAlpha, weighted_anchor_eq_anchor]
  rfl

/-- Transport of a verified executable template to the actual anchor inequalities.
No graph or source theorem is hidden in this bridge. -/
theorem weighted_anchor_nonneg_of_check {t : Counts} (h : checkTemplate t = true)
    (p q i j : Fin (circular t).length) (hpq : p < q) (hij : i < j) :
    0 ≤ Nanuq.Weighted.circularAlpha
      (Nanuq.Weighted.anchorMatrix (rhoFin t) p q) i j := by
  rw [weighted_alpha_eq_alpha]
  exact template_anchor_nonneg h hpq q.isLt hij j.isLt

#print axioms circular_nodup
#print axioms leafIndex_injective
#print axioms weighted_anchor_eq_anchor
#print axioms weighted_alpha_eq_alpha
#print axioms weighted_anchor_nonneg_of_check

end Nanuq.Theta




