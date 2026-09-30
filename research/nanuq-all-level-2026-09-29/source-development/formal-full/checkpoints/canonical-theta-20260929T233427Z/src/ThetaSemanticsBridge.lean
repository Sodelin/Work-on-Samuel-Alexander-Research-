import ThetaFiniteSoundness
import QuartetSemantics

namespace Nanuq.Theta

def Pairing.toResolution : Pairing → Nanuq.Quartet.Resolution
  | .ab_cd => .xy_zw
  | .ac_bd => .xz_yw
  | .ad_bc => .xw_yz

def selectFour (r00 r01 r10 r11 : Pairing) (s : Switching) : Pairing :=
  if s.1 then (if s.2 then r11 else r10) else (if s.2 then r01 else r00)

def distinctRho2 (rs : List Pairing) : ℚ :=
  let qs := rs.eraseDups
  ((2 * (qs.filter fun z => z != Pairing.ab_cd).length : Nat) : ℚ) / (qs.length : ℚ)

/-- Exhaustive equality of the two exact DISTINCT-set representations.
Only four abstract three-valued resolutions are enumerated, not metric answers. -/
theorem four_resolution_average (r00 r01 r10 r11 : Pairing) :
    distinctRho2 [r00,r01,r10,r11] =
      2 * Nanuq.Quartet.sourceMean
        (fun s : Switching => (selectFour r00 r01 r10 r11 s).toResolution) := by
  cases r00 <;> cases r01 <;> cases r10 <;> cases r11 <;> decide +kernel

/-- Explicit resolution map once the strict four-point test succeeds. The
fallback is excluded by the hypotheses of the semantic theorem below. -/
def sourceResolution (t : Counts) (a b c d : Leaf) (s : Switching) :
    Nanuq.Quartet.Resolution :=
  ((quartet t s a b c d).getD Pairing.ab_cd).toResolution

/-- Concrete theta rho is the shared source mean whenever all four computed
switching quartets resolve. No switching-multiplicity mean appears here. -/
theorem rho2_eq_sourceMean_of_resolves (t : Counts) (a b c d : Leaf)
    (r00 r01 r10 r11 : Pairing)
    (h00 : quartet t (false,false) a b c d = some r00)
    (h01 : quartet t (false,true) a b c d = some r01)
    (h10 : quartet t (true,false) a b c d = some r10)
    (h11 : quartet t (true,true) a b c d = some r11) :
    rho2 t a b c d = 2 * Nanuq.Quartet.sourceMean (sourceResolution t a b c d) := by
  have hfun : sourceResolution t a b c d =
      fun s : Switching => (selectFour r00 r01 r10 r11 s).toResolution := by
    funext s
    rcases s with ⟨s1,s2⟩
    cases s1 <;> cases s2 <;>
      simp [sourceResolution, selectFour, h00, h01, h10, h11]
  rw [hfun]
  simpa only [rho2, distinctQuartets, switchings, List.filterMap_cons,
    List.filterMap_nil, h00, h01, h10, h11, Option.toList_some, List.cons_append,
    List.nil_append, distinctRho2] using four_resolution_average r00 r01 r10 r11

#print axioms four_resolution_average
#print axioms rho2_eq_sourceMean_of_resolves
end Nanuq.Theta
