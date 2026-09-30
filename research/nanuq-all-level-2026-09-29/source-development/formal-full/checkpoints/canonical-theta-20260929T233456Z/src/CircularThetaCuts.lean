import AnchorLeafPosition

/-! Every actual switched-theta descendant cut is an interval of canonical
positions, or its complement. No circularity assumption is used. -/
namespace Nanuq.Theta

def armCutStart (t : Counts) (s : Switching) (k : Fin 4) (r : Nat) : Nat :=
  if k = 0 then (if s.1 then 2 + t.b1 + t.b2 + t.a2 + r else 1)
  else if k = 1 then (if s.1 then 0 else 1)
  else if k = 2 then 1 + t.b1 + t.b2 + (if s.2 then 1 else 0)
  else 1 + t.b1 + r

def armCutEnd (t : Counts) (s : Switching) (k : Fin 4) (r : Nat) : Nat :=
  if k = 0 then (if s.1 then t.total + 2 else 2 + t.b1 + t.b2 + t.a2 + r)
  else if k = 1 then t.b1 - r + 1
  else if k = 2 then 1 + t.b1 + t.b2 + t.a2 - r + 1
  else 1 + t.b1 + t.b2 + (if s.2 then 1 else 0)

def armCutComplement (s : Switching) (k : Fin 4) : Prop := k = 0 ∧ s.1 = false

instance (s : Switching) (k : Fin 4) : Decidable (armCutComplement s k) :=
  inferInstanceAs (Decidable (k = 0 ∧ s.1 = false))

theorem armCut_bounds (t : Counts) (s : Switching) (k : Fin 4) (r : Nat)
    (hr : r < t.armLength k) :
    armCutStart t s k r ≤ armCutEnd t s k r ∧
      armCutEnd t s k r ≤ (circular t).length := by
  rcases s with ⟨s1,s2⟩
  rw [circular_length]
  fin_cases k <;> cases s1 <;> cases s2 <;>
    simp +decide [armCutStart, armCutEnd, Counts.armLength, Counts.total] at hr ⊢ <;> omega

theorem arm_cut_interval (t : Counts) (s : Switching) (k : Fin 4) (r : Nat)
    (hr : r < t.armLength k) (x : Leaf) (hx : x ∈ circular t) :
    Vertex.arm k r ∈ terminalPath t s x ↔
      if armCutComplement s k then
        ¬ (armCutStart t s k r ≤ leafPosition t x ∧ leafPosition t x < armCutEnd t s k r)
      else armCutStart t s k r ≤ leafPosition t x ∧ leafPosition t x < armCutEnd t s k r := by
  rw [arm_mem_terminalPath]
  rcases s with ⟨s1,s2⟩
  cases x with
  | c1 =>
    fin_cases k <;> cases s1 <;> cases s2 <;>
      simp +decide [armCutStart, armCutEnd, armCutComplement, switchedArm,
        attachmentDepth, leafPosition, Counts.armLength, Counts.total] at hr ⊢ <;> omega
  | c2 =>
    fin_cases k <;> cases s1 <;> cases s2 <;>
      simp +decide [armCutStart, armCutEnd, armCutComplement, switchedArm,
        attachmentDepth, leafPosition, Counts.armLength, Counts.total] at hr ⊢ <;> omega
  | arm l j =>
    have hj := (arm_mem_circular_iff t l j).mp hx
    fin_cases k <;> fin_cases l <;> cases s1 <;> cases s2 <;>
      simp +decide [armCutStart, armCutEnd, armCutComplement, switchedArm,
        attachmentDepth, leafPosition, Counts.armLength, Counts.total] at hr hj ⊢ <;> omega

theorem attachmentDepth_le_armLength (t : Counts) (s : Switching) (x : Leaf)
    (hx : x ∈ circular t) :
    attachmentDepth t s x ≤ t.armLength (switchedArm s x) := by
  cases x with
  | c1 => simp [attachmentDepth, switchedArm]
  | c2 => simp [attachmentDepth, switchedArm]
  | arm k j =>
    have hj := (arm_mem_circular_iff t k j).mp hx
    simpa only [attachmentDepth, switchedArm] using Nat.succ_le_of_lt hj

theorem central_cut_interval (t : Counts) (s : Switching) :
    ∃ a b : Nat, a ≤ b ∧ b ≤ (circular t).length ∧
      ∀ x ∈ circular t, Vertex.v ∈ terminalPath t s x ↔
        a ≤ leafPosition t x ∧ leafPosition t x < b := by
  refine ⟨(if s.1 then 0 else 1),
    1 + t.b1 + t.b2 + (if s.2 then 1 else 0), ?_, ?_, ?_⟩
  · rcases s with ⟨s1,s2⟩
    cases s1 <;> cases s2 <;> simp <;> omega
  · rw [circular_length]
    rcases s with ⟨s1,s2⟩
    cases s1 <;> cases s2 <;> simp [Counts.total] <;> omega
  · intro x hx
    rw [v_mem_terminalPath]
    rcases s with ⟨s1,s2⟩
    cases x with
    | c1 => cases s1 <;> cases s2 <;> simp [switchedArm, leafPosition] <;> omega
    | c2 => cases s1 <;> cases s2 <;> simp [switchedArm, leafPosition] <;> omega
    | arm k j =>
      have hj := (arm_mem_circular_iff t k j).mp hx
      fin_cases k <;> cases s1 <;> cases s2 <;>
        simp +decide [switchedArm, leafPosition, Counts.armLength] at hj ⊢ <;> omega

/-- A predicate on canonical positions occupies one integer interval, possibly
with the two sides exchanged. Empty and full descendant sets are included. -/
def CanonicalInterval (t : Counts) (P : Fin (circular t).length → Prop) : Prop :=
  ∃ a b : Nat, a ≤ b ∧ b ≤ (circular t).length ∧
    ((∀ i, P i ↔ a ≤ i.val ∧ i.val < b) ∨
      (∀ i, P i ↔ ¬ (a ≤ i.val ∧ i.val < b)))

theorem terminalPath_cut_interval (t : Counts) (s : Switching) (z : Vertex) :
    CanonicalInterval t (fun i => z ∈ terminalPath t s (leafIndex t i)) := by
  cases z with
  | u =>
    refine ⟨0, (circular t).length, Nat.zero_le _, le_rfl, Or.inl ?_⟩
    intro i
    simp [i.isLt]
  | v =>
    obtain ⟨a,b,hab,hb,hpred⟩ := central_cut_interval t s
    refine ⟨a,b,hab,hb,Or.inl ?_⟩
    intro i
    simpa only [leafPosition_leafIndex] using hpred (leafIndex t i) (leafIndex_mem_circular t i)
  | arm k r =>
    by_cases hr : r < t.armLength k
    · obtain ⟨hab,hb⟩ := armCut_bounds t s k r hr
      refine ⟨armCutStart t s k r,armCutEnd t s k r,hab,hb,?_⟩
      by_cases hc : armCutComplement s k
      · refine Or.inr ?_
        intro i
        simpa only [hc, if_true, leafPosition_leafIndex] using
          arm_cut_interval t s k r hr (leafIndex t i) (leafIndex_mem_circular t i)
      · refine Or.inl ?_
        intro i
        simpa only [hc, if_false, leafPosition_leafIndex] using
          arm_cut_interval t s k r hr (leafIndex t i) (leafIndex_mem_circular t i)
    · refine ⟨0,0,le_rfl,Nat.zero_le _,Or.inl ?_⟩
      intro i
      have hd := attachmentDepth_le_armLength t s (leafIndex t i) (leafIndex_mem_circular t i)
      dsimp only
      rw [arm_mem_terminalPath]
      simp only [Nat.not_lt_zero, and_false, iff_false, not_and]
      intro hsame hlt
      rw [hsame] at hd
      exact hr (lt_of_lt_of_le hlt hd)
  | terminal x =>
    by_cases hx : x ∈ circular t
    · have hp := leafPosition_lt t hx
      refine ⟨leafPosition t x, leafPosition t x + 1, Nat.le_succ _,
        Nat.succ_le_of_lt hp, Or.inl ?_⟩
      intro i
      dsimp only
      rw [terminal_mem_terminalPath]
      have he : x = leafIndex t i ↔ leafPosition t x = i.val := by
        constructor
        · intro h; simpa only [h, leafPosition_leafIndex]
        · intro h
          calc
            x = leafAt t (leafPosition t x) := (leafAt_leafPosition t hx).symm
            _ = leafIndex t i := by rw [h]; rfl
      rw [he]
      omega
    · refine ⟨0,0,le_rfl,Nat.zero_le _,Or.inl ?_⟩
      intro i
      dsimp only
      rw [terminal_mem_terminalPath]
      have hi := leafIndex_mem_circular t i
      simp only [Nat.not_lt_zero, and_false, iff_false]
      intro he
      exact hx (he.symm ▸ hi)

#print axioms arm_cut_interval
#print axioms terminalPath_cut_interval
end Nanuq.Theta

