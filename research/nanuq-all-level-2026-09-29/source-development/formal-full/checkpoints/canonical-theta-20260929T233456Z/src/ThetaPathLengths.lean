import ThetaArmMetric
import ThetaQuartetValidity
import AnchorCompressionOrder

namespace Nanuq.Theta

def armTailPath (k : Fin 4) (start depth : Nat) (x : Leaf) : List Vertex :=
  (List.range' start depth).map (Vertex.arm k) ++ [Vertex.terminal x]

theorem tail_common_same (k : Fin 4) (start m n : Nat) (x y : Leaf) (hxy : x ≠ y) :
    commonPrefixLength (armTailPath k start m x) (armTailPath k start n y) = min m n := by
  induction m generalizing start n with
  | zero => cases n <;> simp [armTailPath, List.range'_succ, commonPrefixLength, hxy]
  | succ m ih =>
    cases n with
    | zero => simp [armTailPath, List.range'_succ, commonPrefixLength]
    | succ n =>
      have hh := congrArg (fun z => 1 + z) (ih (start + 1) n)
      simp [armTailPath, List.range'_succ, commonPrefixLength] at hh ⊢
      omega

theorem tail_common_different (k r : Fin 4) (hkr : k ≠ r)
    (start m n : Nat) (x y : Leaf) (hxy : x ≠ y) :
    commonPrefixLength (armTailPath k start m x) (armTailPath r start n y) = 0 := by
  cases m <;> cases n <;>
    simp [armTailPath, List.range'_succ, commonPrefixLength, hxy, hkr]

theorem tail_common (k r : Fin 4) (start m n : Nat) (x y : Leaf) (hxy : x ≠ y) :
    commonPrefixLength (armTailPath k start m x) (armTailPath r start n y) =
      if k = r then min m n else 0 := by
  by_cases hkr : k = r
  · subst r
    simp only [if_true]
    exact tail_common_same k start m n x y hxy
  · rw [if_neg hkr]
    exact tail_common_different k r hkr start m n x y hxy

theorem common_v_tail (ys : List Vertex) (k : Fin 4) (start m : Nat) (x : Leaf) :
    commonPrefixLength (Vertex.v :: ys) (armTailPath k start m x) = 0 := by
  cases m <;> simp [armTailPath, List.range'_succ, commonPrefixLength]

theorem common_tail_v (k : Fin 4) (start m : Nat) (x : Leaf) (ys : List Vertex) :
    commonPrefixLength (armTailPath k start m x) (Vertex.v :: ys) = 0 := by
  rw [commonPrefixLength_comm]
  exact common_v_tail ys k start m x

theorem based_path_eq (k : Fin 4) (m : Nat) (x : Leaf) :
    armPath k m ++ [Vertex.terminal x] =
      Vertex.u :: ((if k.val % 2 = 1 then [Vertex.v] else []) ++ armTailPath k 0 m x) := by
  simp [armPath, armTailPath, List.range_eq_range', List.append_assoc]

theorem based_common (k r : Fin 4) (m n : Nat) (x y : Leaf) (hxy : x ≠ y) :
    commonPrefixLength (armPath k m ++ [Vertex.terminal x])
      (armPath r n ++ [Vertex.terminal y]) =
      1 + (if k.val % 2 = 1 ∧ r.val % 2 = 1 then 1 else 0) +
        (if k = r then min m n else 0) := by
  rw [based_path_eq, based_path_eq]
  by_cases hk : k.val % 2 = 1 <;> by_cases hr : r.val % 2 = 1
  · simp [hk, hr, commonPrefixLength, tail_common k r 0 m n x y hxy]
    omega
  · have hkr : k ≠ r := by intro h; subst r; exact hr hk
    simp [hk, hr, hkr, commonPrefixLength, common_v_tail]
  · have hkr : k ≠ r := by intro h; subst r; exact hk hr
    simp [hk, hr, hkr, commonPrefixLength, common_tail_v]
  · simp [hk, hr, commonPrefixLength, tail_common k r 0 m n x y hxy]

theorem based_distance (k r : Fin 4) (m n : Nat) (x y : Leaf) (hxy : x ≠ y) :
    (armPath k m ++ [Vertex.terminal x]).length +
      (armPath r n ++ [Vertex.terminal y]).length -
      2 * commonPrefixLength (armPath k m ++ [Vertex.terminal x])
        (armPath r n ++ [Vertex.terminal y]) = hDistance k r m n := by
  rw [based_common k r m n x y hxy]
  fin_cases k <;> fin_cases r
  all_goals simp [armPath, hDistance]
  all_goals omega

def switchedArm (s : Switching) : Leaf → Fin 4
  | .c1 => if s.1 then 1 else 0
  | .c2 => if s.2 then 3 else 2
  | .arm k _ => k

def attachmentDepth (t : Counts) (s : Switching) : Leaf → Nat
  | .c1 => t.armLength (switchedArm s .c1)
  | .c2 => t.armLength (switchedArm s .c2)
  | .arm _ j => j + 1

def hybridBump : Leaf → Nat
  | .c1 => 1
  | .c2 => 1
  | .arm _ _ => 0

def metricPosition (t : Counts) (s : Switching) (x : Leaf) : Nat :=
  attachmentDepth t s x + hybridBump x

theorem metricPosition_pos (t : Counts) (s : Switching) (x : Leaf) :
    0 < metricPosition t s x := by
  cases x <;> simp [metricPosition, attachmentDepth, hybridBump]

theorem terminalPath_eq_based (t : Counts) (s : Switching) (x : Leaf) :
    terminalPath t s x = armPath (switchedArm s x) (attachmentDepth t s x) ++
      [Vertex.terminal x] := by
  cases x <;> rfl

theorem treeDistance_eq_hDistance (t : Counts) (s : Switching) (x y : Leaf) (hxy : x ≠ y) :
    treeDistance t s x y =
      hDistance (switchedArm s x) (switchedArm s y)
        (attachmentDepth t s x) (attachmentDepth t s y) := by
  simpa only [treeDistance, terminalPath_eq_based] using
    based_distance (switchedArm s x) (switchedArm s y)
      (attachmentDepth t s x) (attachmentDepth t s y) x y hxy

#print axioms treeDistance_eq_hDistance
end Nanuq.Theta
