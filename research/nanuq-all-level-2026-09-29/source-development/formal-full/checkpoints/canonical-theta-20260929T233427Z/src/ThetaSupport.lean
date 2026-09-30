import ThetaFiniteSoundness

namespace Nanuq.Theta

deriving instance ReflBEq for Leaf
deriving instance LawfulBEq for Leaf
deriving instance ReflBEq for Vertex
deriving instance LawfulBEq for Vertex

/-- The proper nonempty circular interval between gaps i<j. -/
def onGapSide (i j k : Nat) : Bool := decide (i < k ∧ k ≤ j)

/-- An edge of one explicit rooted-path switching tree realizes this circular
split. Its child vertex partitions terminal paths by membership. Both split
orientations are checked; unlabeled tips and root stems cannot match a proper
nonempty split and therefore do not create spurious support. -/
def displayedSplit (t : Counts) (i j : Nat) : Bool :=
  switchings.any fun s =>
    (switchingEdges t s).any fun e =>
      ((List.range (circular t).length).all fun k =>
        decide (e.2 ∈ terminalPath t s (leafAt t k)) == onGapSide i j k) ||
      ((List.range (circular t).length).all fun k =>
        decide (e.2 ∈ terminalPath t s (leafAt t k)) == !(onGapSide i j k))

def positiveAnchorAt (t : Counts) (i j : Nat) : Bool :=
  (pairs (circular t).length).any fun pq => decide (0 < alpha t pq.1 pq.2 i j)

/-- Exact support equality, in addition to (separately checked) positivity. -/
def checkSupport (t : Counts) : Bool :=
  (pairs (circular t).length).all fun ij =>
    positiveAnchorAt t ij.1 ij.2 == displayedSplit t ij.1 ij.2

theorem support_iff_of_check {t : Counts} (ht : checkSupport t = true)
    {i j : Nat} (hij : i < j) (hj : j < (circular t).length) :
    displayedSplit t i j = true ↔
      ∃ p q, p < q ∧ q < (circular t).length ∧ 0 < alpha t p q i j := by
  have hp : (i,j) ∈ pairs (circular t).length := mem_pairs.mpr ⟨hij,hj⟩
  have heq : positiveAnchorAt t i j = displayedSplit t i j := by
    simpa using List.all_eq_true.mp ht (i,j) hp
  constructor
  · intro hd
    have hpos : positiveAnchorAt t i j = true := heq.trans hd
    obtain ⟨⟨p,q⟩, hpq, ha⟩ := List.any_eq_true.mp hpos
    exact ⟨p,q,(mem_pairs.mp hpq).1,(mem_pairs.mp hpq).2,of_decide_eq_true ha⟩
  · rintro ⟨p,q,hpq,hq,ha⟩
    rw [← heq]
    exact List.any_eq_true.mpr ⟨(p,q),mem_pairs.mpr ⟨hpq,hq⟩,by simpa using ha⟩

#print axioms support_iff_of_check
end Nanuq.Theta
