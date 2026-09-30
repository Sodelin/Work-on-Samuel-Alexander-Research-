import ThetaSupportCertificate
import AnchorThetaBridge
import ThetaSourceExact

/-! Import-only assembly endpoint for the COMPLETE bounded canonical-theta
certificate. This is not the arbitrary-arm or raw-network theorem. -/
namespace Nanuq.Theta

theorem bounded_source_mean (t : Counts)
    (hlo : 1 ≤ t.total) (hhi : t.total ≤ 6)
    (a b c d : Fin (circular t).length)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    rhoFin t a b c d = Nanuq.Quartet.sourceMean
      (sourceResolution t (leafIndex t a) (leafIndex t b) (leafIndex t c) (leafIndex t d)) :=
  rhoFin_source_of_checked (bounded_quartets_checked t hlo hhi) a b c d hab hac had hbc hbd hcd

theorem bounded_weighted_anchor_nonnegative (t : Counts)
    (hlo : 1 ≤ t.total) (hhi : t.total ≤ 6)
    (p q i j : Fin (circular t).length) (hpq : p < q) (hij : i < j) :
    0 ≤ Nanuq.Weighted.circularAlpha
      (Nanuq.Weighted.anchorMatrix (rhoFin t) p q) i j := by
  rw [weighted_alpha_eq_alpha]
  exact bounded_anchor_nonnegative t hlo hhi hpq q.isLt hij j.isLt

theorem bounded_weighted_support_exact (t : Counts)
    (hlo : 1 ≤ t.total) (hhi : t.total ≤ 6)
    (i j : Fin (circular t).length) (hij : i < j) :
    displayedSplit t i.val j.val = true ↔
      ∃ p q : Fin (circular t).length, p < q ∧
        0 < Nanuq.Weighted.circularAlpha
          (Nanuq.Weighted.anchorMatrix (rhoFin t) p q) i j := by
  rw [bounded_support_exact t hlo hhi hij j.isLt]
  constructor
  · rintro ⟨p,q,hpq,hq,ha⟩
    refine ⟨⟨p,lt_trans hpq hq⟩,⟨q,hq⟩,hpq,?_⟩
    simpa only [weighted_alpha_eq_alpha] using ha
  · rintro ⟨p,q,hpq,ha⟩
    exact ⟨p.val,q.val,hpq,q.isLt,by simpa only [weighted_alpha_eq_alpha] using ha⟩

#print axioms all_templates_checked
#print axioms exact_coefficient_count
#print axioms bounded_source_mean
#print axioms bounded_weighted_anchor_nonnegative
#print axioms bounded_weighted_support_exact
end Nanuq.Theta
