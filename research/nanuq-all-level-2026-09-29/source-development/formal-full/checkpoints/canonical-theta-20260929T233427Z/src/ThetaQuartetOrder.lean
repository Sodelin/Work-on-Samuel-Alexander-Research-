import ThetaBumpedMetric
import ThetaArmOrder

namespace Nanuq.Theta

theorem first_minimum_iff_cut (t : Counts) (s : Switching) (a b c d : Leaf)
    (ha : a ∈ circular t) (hb : b ∈ circular t) (hc : c ∈ circular t) (hd : d ∈ circular t)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (treeDistance t s a b + treeDistance t s c d < treeDistance t s a c + treeDistance t s b d ∧
      treeDistance t s a b + treeDistance t s c d < treeDistance t s a d + treeDistance t s b c) ↔
    hPairCut (switchedArm s a) (switchedArm s b) (switchedArm s c) (switchedArm s d)
      (metricPosition t s a) (metricPosition t s b) (metricPosition t s c) (metricPosition t s d) := by
  have hchar := hDistance_pair_cut (switchedArm s a) (switchedArm s b)
    (switchedArm s c) (switchedArm s d)
    (metricPosition t s a) (metricPosition t s b) (metricPosition t s c) (metricPosition t s d)
    (metricPosition_pos t s a) (metricPosition_pos t s b)
    (metricPosition_pos t s c) (metricPosition_pos t s d)
  rw [metricPosition_distance t s a b ha hb hab,
    metricPosition_distance t s c d hc hd hcd,
    metricPosition_distance t s a c ha hc hac,
    metricPosition_distance t s b d hb hd hbd,
    metricPosition_distance t s a d ha hd had,
    metricPosition_distance t s b c hb hc hbc] at hchar
  constructor
  · intro h
    apply hchar.mp
    constructor <;> omega
  · intro h
    have hz := hchar.mpr h
    constructor <;> omega

/-- Actual executable four-point quartets depend only on switched arm tags and
relative position order. This theorem has no bound on any arm length. -/
theorem quartet_eq_orderQuartet (t : Counts) (s : Switching) (a b c d : Leaf)
    (ha : a ∈ circular t) (hb : b ∈ circular t) (hc : c ∈ circular t) (hd : d ∈ circular t)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    quartet t s a b c d = orderQuartet (switchedArm s) (metricPosition t s) a b c d := by
  have h0 := first_minimum_iff_cut t s a b c d ha hb hc hd hab hac had hbc hbd hcd
  have h1 := first_minimum_iff_cut t s a c b d ha hc hb hd hac hab had (Ne.symm hbc) hcd hbd
  have h2 := first_minimum_iff_cut t s a d b c ha hd hb hc had hab hac (Ne.symm hbd) (Ne.symm hcd) hbc
  rw [treeDistance_comm t s c b] at h1
  rw [treeDistance_comm t s d c, treeDistance_comm t s d b] at h2
  dsimp only [quartet, orderQuartet]
  simp only [h0,h1,h2]

#print axioms quartet_eq_orderQuartet
end Nanuq.Theta
