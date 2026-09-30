import ThetaSwitchingEdges
import ThetaQuartetOrder

/-! Concrete edge witnesses for the executable four-point quartet test. -/
namespace Nanuq.Theta

/-- For two distinct leaves on one switched arm, the smaller (bumped) metric
position is attained by an ordinary leaf and lies within both actual paths. -/
theorem min_position_le_depths (t : Counts) (s : Switching) (a b : Leaf)
    (ha : a ∈ circular t) (hb : b ∈ circular t) (hab : a ≠ b)
    (hsame : switchedArm s a = switchedArm s b) :
    min (metricPosition t s a) (metricPosition t s b) ≤ attachmentDepth t s a ∧
      min (metricPosition t s a) (metricPosition t s b) ≤ attachmentDepth t s b := by
  have had := attachmentDepth_le t s a ha
  have hbd := attachmentDepth_le t s b hb
  rcases hybridBump_cases a with ha0 | ha1 <;> rcases hybridBump_cases b with hb0 | hb1
  · simp only [metricPosition,ha0,hb0,Nat.add_zero]
    exact ⟨Nat.min_le_left _ _,Nat.min_le_right _ _⟩
  · have hbdepth := hybrid_depth_eq t s b hb1
    rw [hsame] at had
    simp only [metricPosition,ha0,hb1,Nat.add_zero]
    constructor <;> omega
  · have hadepth := hybrid_depth_eq t s a ha1
    rw [← hsame] at hbd
    simp only [metricPosition,ha1,hb0,Nat.add_zero]
    constructor <;> omega
  · exact False.elim ((switched_hybrids_different s a b ha1 hb1 hab) hsame)

def cutSeparatesPairs (t : Counts) (s : Switching) (z : Vertex) (a b c d : Leaf) : Prop :=
  (z ∈ terminalPath t s a ∧ z ∈ terminalPath t s b ∧
    z ∉ terminalPath t s c ∧ z ∉ terminalPath t s d) ∨
  (z ∉ terminalPath t s a ∧ z ∉ terminalPath t s b ∧
    z ∈ terminalPath t s c ∧ z ∈ terminalPath t s d)

/-- An arm-tail alternative has a genuine edge with exactly the requested
membership pattern on the four leaves. -/
theorem edge_of_tailPair (t : Counts) (s : Switching) (a b c d : Leaf)
    (ha : a ∈ circular t) (hb : b ∈ circular t) (hab : a ≠ b)
    (htail : tailPair (switchedArm s a) (switchedArm s b) (switchedArm s c) (switchedArm s d)
      (metricPosition t s a) (metricPosition t s b) (metricPosition t s c) (metricPosition t s d)) :
    ∃ y z, (y,z) ∈ switchingEdges t s ∧
      z ∈ terminalPath t s a ∧ z ∈ terminalPath t s b ∧
      z ∉ terminalPath t s c ∧ z ∉ terminalPath t s d := by
  obtain ⟨hsame,hc,hd⟩ := htail
  let m := min (metricPosition t s a) (metricPosition t s b)
  let z := Vertex.arm (switchedArm s a) (m - 1)
  have hm : 0 < m := lt_min (metricPosition_pos t s a) (metricPosition_pos t s b)
  have hdepth := min_position_le_depths t s a b ha hb hab hsame
  have hza : z ∈ terminalPath t s a := by
    simp only [z,arm_mem_terminalPath,true_and]
    change m - 1 < attachmentDepth t s a
    change m ≤ attachmentDepth t s a ∧ m ≤ attachmentDepth t s b at hdepth
    omega
  have hzb : z ∈ terminalPath t s b := by
    simp only [z,arm_mem_terminalPath,hsame,true_and]
    change m - 1 < attachmentDepth t s b
    change m ≤ attachmentDepth t s a ∧ m ≤ attachmentDepth t s b at hdepth
    omega
  have hout (x : Leaf)
      (h : switchedArm s x ≠ switchedArm s a ∨
        (metricPosition t s x < metricPosition t s a ∧ metricPosition t s x < metricPosition t s b)) :
      z ∉ terminalPath t s x := by
    rw [show z = Vertex.arm (switchedArm s a) (m - 1) from rfl,arm_mem_terminalPath]
    intro hz
    rcases h with hne | hlt
    · exact hne hz.1
    · have hxm : metricPosition t s x < m := lt_min hlt.1 hlt.2
      have hxd : attachmentDepth t s x ≤ metricPosition t s x := by
        simp [metricPosition]
      omega
  obtain ⟨y,he⟩ := exists_switching_edge_of_path t s a ha z hza (by simp [z])
  exact ⟨y,z,he,hza,hzb,hout c hc,hout d hd⟩

/-- The four-point cut criterion always has an actual switched-tree edge witness. -/
theorem edge_of_hPairCut (t : Counts) (s : Switching) (a b c d : Leaf)
    (ha : a ∈ circular t) (hb : b ∈ circular t) (hc : c ∈ circular t) (hd : d ∈ circular t)
    (hab : a ≠ b) (hcd : c ≠ d)
    (hcut : hPairCut (switchedArm s a) (switchedArm s b) (switchedArm s c) (switchedArm s d)
      (metricPosition t s a) (metricPosition t s b) (metricPosition t s c) (metricPosition t s d)) :
    ∃ y z, (y,z) ∈ switchingEdges t s ∧ cutSeparatesPairs t s z a b c d := by
  rcases hcut with htail | htail | hcentral
  · obtain ⟨y,z,he,hza,hzb,hzc,hzd⟩ := edge_of_tailPair t s a b c d ha hb hab htail
    exact ⟨y,z,he,Or.inl ⟨hza,hzb,hzc,hzd⟩⟩
  · obtain ⟨y,z,he,hzc,hzd,hza,hzb⟩ := edge_of_tailPair t s c d a b hc hd hcd htail
    exact ⟨y,z,he,Or.inr ⟨hza,hzb,hzc,hzd⟩⟩
  · obtain ⟨hpab,hpcd,hpne⟩ := hcentral
    have hpa := Nat.mod_lt (switchedArm s a).val (by decide : 0 < 2)
    have hpc := Nat.mod_lt (switchedArm s c).val (by decide : 0 < 2)
    by_cases hodd : (switchedArm s a).val % 2 = 1
    · have hza : Vertex.v ∈ terminalPath t s a := (v_mem_terminalPath t s a).mpr hodd
      have hzb : Vertex.v ∈ terminalPath t s b := by rw [v_mem_terminalPath]; omega
      have hzc : Vertex.v ∉ terminalPath t s c := by rw [v_mem_terminalPath]; omega
      have hzd : Vertex.v ∉ terminalPath t s d := by rw [v_mem_terminalPath]; omega
      obtain ⟨y,he⟩ := exists_switching_edge_of_path t s a ha Vertex.v hza (by decide)
      exact ⟨y,Vertex.v,he,Or.inl ⟨hza,hzb,hzc,hzd⟩⟩
    · have hza : Vertex.v ∉ terminalPath t s a := by rw [v_mem_terminalPath]; exact hodd
      have hzb : Vertex.v ∉ terminalPath t s b := by rw [v_mem_terminalPath]; omega
      have hzc : Vertex.v ∈ terminalPath t s c := by rw [v_mem_terminalPath]; omega
      have hzd : Vertex.v ∈ terminalPath t s d := by rw [v_mem_terminalPath]; omega
      obtain ⟨y,he⟩ := exists_switching_edge_of_path t s c hc Vertex.v hzc (by decide)
      exact ⟨y,Vertex.v,he,Or.inr ⟨hza,hzb,hzc,hzd⟩⟩

/-- Actual quartet resolution provides an actual separating edge. -/
theorem edge_of_quartet (t : Counts) (s : Switching) (a b c d : Leaf)
    (ha : a ∈ circular t) (hb : b ∈ circular t) (hc : c ∈ circular t) (hd : d ∈ circular t)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hq : quartet t s a b c d = some Pairing.ab_cd) :
    ∃ y z, (y,z) ∈ switchingEdges t s ∧ cutSeparatesPairs t s z a b c d := by
  have hmin :
      treeDistance t s a b + treeDistance t s c d < treeDistance t s a c + treeDistance t s b d ∧
      treeDistance t s a b + treeDistance t s c d < treeDistance t s a d + treeDistance t s b c := by
    dsimp only [quartet] at hq
    split_ifs at hq with h0 h1 h2
    · exact h0
    all_goals cases hq
  exact edge_of_hPairCut t s a b c d ha hb hc hd hab hcd
    ((first_minimum_iff_cut t s a b c d ha hb hc hd hab hac had hbc hbd hcd).mp hmin)

#print axioms min_position_le_depths
#print axioms edge_of_hPairCut
#print axioms edge_of_quartet
end Nanuq.Theta