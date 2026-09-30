import ThetaQuartetEdge

namespace Nanuq.Theta

/-- On a valid common arm, strict actual-depth ordering also orders the
metric positions. An excluded hybrid cannot lie before a retained ordinary leaf. -/
theorem position_lt_of_depth_lt (t : Counts) (s : Switching) (x y : Leaf)
    (hy : y ∈ circular t) (hsame : switchedArm s x = switchedArm s y)
    (hdepth : attachmentDepth t s x < attachmentDepth t s y) :
    metricPosition t s x < metricPosition t s y := by
  rcases hybridBump_cases x with hx0 | hx1
  · simp only [metricPosition,hx0,Nat.add_zero]
    omega
  · have hdx := hybrid_depth_eq t s x hx1
    have hdy := attachmentDepth_le t s y hy
    rw [← hsame] at hdy
    omega

/-- The explicit descendant predicates force the same four-point cut whenever
a vertex contains a,b and excludes c,d. -/
theorem hPairCut_of_path_partition (t : Counts) (s : Switching) (z : Vertex) (a b c d : Leaf)
    (ha : a ∈ circular t) (hb : b ∈ circular t) (hab : a ≠ b)
    (hza : z ∈ terminalPath t s a) (hzb : z ∈ terminalPath t s b)
    (hzc : z ∉ terminalPath t s c) (hzd : z ∉ terminalPath t s d) :
    hPairCut (switchedArm s a) (switchedArm s b) (switchedArm s c) (switchedArm s d)
      (metricPosition t s a) (metricPosition t s b) (metricPosition t s c) (metricPosition t s d) := by
  cases z with
  | u => exact False.elim (hzc (u_mem_terminalPath t s c))
  | v =>
    simp only [v_mem_terminalPath] at hza hzb hzc hzd
    have hpc := Nat.mod_lt (switchedArm s c).val (by decide : 0 < 2)
    have hpd := Nat.mod_lt (switchedArm s d).val (by decide : 0 < 2)
    refine Or.inr (Or.inr ?_)
    unfold centralPair
    constructor
    · omega
    · constructor <;> omega
  | arm k r =>
    rw [arm_mem_terminalPath] at hza hzb hzc hzd
    have hsame : switchedArm s a = switchedArm s b := hza.1.trans hzb.1.symm
    have hother (x : Leaf)
        (hout : ¬ (switchedArm s x = k ∧ r < attachmentDepth t s x)) :
        switchedArm s x ≠ switchedArm s a ∨
          (metricPosition t s x < metricPosition t s a ∧ metricPosition t s x < metricPosition t s b) := by
      by_cases heq : switchedArm s x = switchedArm s a
      · right
        have hxr : attachmentDepth t s x ≤ r := by
          by_contra hnot
          exact hout ⟨heq.trans hza.1,by omega⟩
        exact ⟨position_lt_of_depth_lt t s x a ha heq (by omega),
          position_lt_of_depth_lt t s x b hb (heq.trans hsame) (by omega)⟩
      · exact Or.inl heq
    exact Or.inl ⟨hsame,hother c hzc,hother d hzd⟩
  | terminal x =>
    rw [terminal_mem_terminalPath] at hza hzb
    exact False.elim (hab (hza.symm.trans hzb))

/-- Either orientation of a concrete separating cut gives the strict
four-point cut for the same unordered pair partition. -/
theorem hPairCut_of_cutSeparatesPairs (t : Counts) (s : Switching) (z : Vertex) (a b c d : Leaf)
    (ha : a ∈ circular t) (hb : b ∈ circular t) (hc : c ∈ circular t) (hd : d ∈ circular t)
    (hab : a ≠ b) (hcd : c ≠ d) (hsep : cutSeparatesPairs t s z a b c d) :
    hPairCut (switchedArm s a) (switchedArm s b) (switchedArm s c) (switchedArm s d)
      (metricPosition t s a) (metricPosition t s b) (metricPosition t s c) (metricPosition t s d) := by
  rcases hsep with ⟨hza,hzb,hzc,hzd⟩ | ⟨hza,hzb,hzc,hzd⟩
  · exact hPairCut_of_path_partition t s z a b c d ha hb hab hza hzb hzc hzd
  · have hcut := hPairCut_of_path_partition t s z c d a b hc hd hcd hzc hzd hza hzb
    rcases hcut with htail | htail | hcentral
    · exact Or.inr (Or.inl htail)
    · exact Or.inl htail
    · exact Or.inr (Or.inr ⟨hcentral.2.1,hcentral.1,Ne.symm hcentral.2.2⟩)

theorem quartet_of_cutSeparatesPairs (t : Counts) (s : Switching) (z : Vertex) (a b c d : Leaf)
    (ha : a ∈ circular t) (hb : b ∈ circular t) (hc : c ∈ circular t) (hd : d ∈ circular t)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hsep : cutSeparatesPairs t s z a b c d) :
    quartet t s a b c d = some Pairing.ab_cd := by
  rw [quartet_eq_orderQuartet t s a b c d ha hb hc hd hab hac had hbc hbd hcd]
  have hcut := hPairCut_of_cutSeparatesPairs t s z a b c d ha hb hc hd hab hcd hsep
  simp only [orderQuartet,hcut,if_true]

/-- The executable four-point test agrees exactly with separation by an
actual edge of the same switched tree. No circular-order assumption is used. -/
theorem quartet_iff_separating_edge (t : Counts) (s : Switching) (a b c d : Leaf)
    (ha : a ∈ circular t) (hb : b ∈ circular t) (hc : c ∈ circular t) (hd : d ∈ circular t)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    quartet t s a b c d = some Pairing.ab_cd ↔
      ∃ y z, (y,z) ∈ switchingEdges t s ∧ cutSeparatesPairs t s z a b c d := by
  constructor
  · exact edge_of_quartet t s a b c d ha hb hc hd hab hac had hbc hbd hcd
  · rintro ⟨y,z,_he,hsep⟩
    exact quartet_of_cutSeparatesPairs t s z a b c d ha hb hc hd hab hac had hbc hbd hcd hsep

#print axioms hPairCut_of_path_partition
#print axioms quartet_iff_separating_edge
end Nanuq.Theta