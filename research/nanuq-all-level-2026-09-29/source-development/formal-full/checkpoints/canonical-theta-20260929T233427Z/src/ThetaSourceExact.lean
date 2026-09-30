import ThetaQuartetValidity
import ThetaSemanticsBridge
import Mathlib.Tactic.Ring

namespace Nanuq.Theta

/-- The checker eliminates the fallback in `sourceResolution` for every
ordering of four distinct valid leaf indices, not only increasing indices. -/
theorem rho2_source_of_checked {t : Counts} (h : checkQuartets t = true)
    (a b c d : Nat)
    (ha : a < (circular t).length) (hb : b < (circular t).length)
    (hc : c < (circular t).length) (hd : d < (circular t).length)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    rho2 t (leafAt t a) (leafAt t b) (leafAt t c) (leafAt t d) =
      2 * Nanuq.Quartet.sourceMean
        (sourceResolution t (leafAt t a) (leafAt t b) (leafAt t c) (leafAt t d)) := by
  have hr := resolves_of_check h a b c d ha hb hc hd hab hac had hbc hbd hcd
  obtain ⟨r00,h00⟩ := Option.isSome_iff_exists.mp (hr (false,false))
  obtain ⟨r01,h01⟩ := Option.isSome_iff_exists.mp (hr (false,true))
  obtain ⟨r10,h10⟩ := Option.isSome_iff_exists.mp (hr (true,false))
  obtain ⟨r11,h11⟩ := Option.isSome_iff_exists.mp (hr (true,true))
  exact rho2_eq_sourceMean_of_resolves t _ _ _ _ r00 r01 r10 r11 h00 h01 h10 h11

theorem rhoFin_source_of_checked {t : Counts} (h : checkQuartets t = true)
    (a b c d : Fin (circular t).length)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    rhoFin t a b c d = Nanuq.Quartet.sourceMean
      (sourceResolution t (leafIndex t a) (leafIndex t b) (leafIndex t c) (leafIndex t d)) := by
  have hr := rho2_source_of_checked h a.val b.val c.val d.val a.isLt b.isLt c.isLt d.isLt
    (fun z => hab (Fin.ext z)) (fun z => hac (Fin.ext z)) (fun z => had (Fin.ext z))
    (fun z => hbc (Fin.ext z)) (fun z => hbd (Fin.ext z)) (fun z => hcd (Fin.ext z))
  dsimp only [rhoFin, leafIndex]
  rw [hr]
  ring

#print axioms rho2_source_of_checked
#print axioms rhoFin_source_of_checked
end Nanuq.Theta
