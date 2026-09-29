import SamuelAlexanderResearch.FiniteEditExact

/-! Executable finite residual maxima and attained sharp-tail witnesses. The global cutoff is justified in FiniteEditOptimum. -/
namespace FiniteEditAlgorithm

open BinaryAvoidance QuantitativeAvoidance FiniteEditStability PhaseShift PhaseHeight

def residual (s : Nat → Bool) (m v : Nat) : Int :=
  3*(FiniteEditExact.height s m v : Int)-8*(v : Int)

/-- Maximum residual over exactly the positive starts 1 through n+1. -/
def best (s : Nat → Bool) (m : Nat) : Nat → Int
  | 0 => residual s m 1
  | n+1 =>
    if best s m n ≤ residual s m (n+2) then residual s m (n+2) else best s m n

theorem residual_le_best (s : Nat → Bool) (m n v : Nat)
    (hv : 1≤v) (hn : v≤n+1) : residual s m v ≤ best s m n := by
  induction n with
  | zero =>
    have he : v=1 := by omega
    subst v
    exact Int.le_refl _
  | succ n ih =>
    by_cases he : v=n+2
    · subst v
      simp only [best]
      split <;> omega
    · have hprev := ih (by omega)
      simp only [best]
      split <;> omega

theorem best_attained (s : Nat → Bool) (m n : Nat) :
    ∃ v, 1≤v ∧ v≤n+1 ∧ residual s m v=best s m n := by
  induction n with
  | zero => exact ⟨1,by omega,by omega,rfl⟩
  | succ n ih =>
    obtain ⟨v,hv,hn,he⟩ := ih
    simp only [best]
    split
    · exact ⟨n+2,by omega,by omega,rfl⟩
    · exact ⟨v,hv,by omega,he⟩

/-- Every sufficiently large dyadic extremal suffix admits an edited prefix.
The starting vertex never exceeds the unedited extremal start. -/
theorem sharp_tail_witness (s : Nat → Bool) (m n : Nat)
    (hag : AgreeFrom s ThueMorseBits.t m) (hlarge : m+1≤2^n) :
    ∃ v, 1≤v ∧ v≤3*2^n-1 ∧ 3*2^n-1≤v+m ∧
      HasPrefix s v (8*2^n-3) := by
  let q := 2^n
  have hq : 0<q := Nat.two_pow_pos n
  have hm : m+1≤q := hlarge
  let w := 3*q+m-1
  obtain ⟨path,hend,hmatch,hlo,hhi⟩ := backward_prefix s m w (by dsimp [w]; omega)
  have hv : 1≤path 0 := by dsimp [w] at *; omega
  have front : w ∈ frontier s (path 0) m :=
    (mem_frontier s (path 0) m w).mpr ⟨path,rfl,hend,hmatch⟩
  have tail : HasPrefix (shift ThueMorseBits.t m) (w-2*m) (8*q-m-3) := by
    have hi : w-2*m=3*q-m-1 := by dsimp [w]; omega
    rw [hi]
    exact PhaseExtremal.shifted_family_prefix n m (by omega)
  have whole := (FiniteEditExact.prefix_decomposition s ThueMorseBits.t m hag
    (path 0) (8*q-m-3)).mpr ⟨w,front,tail⟩
  have hlen : m+(8*q-m-3)=8*q-3 := by omega
  rw [hlen] at whole
  refine ⟨path 0,hv,?_,?_,whole⟩ <;> dsimp [w] at * <;> omega

/-- A deliberately generous computable cutoff: two large successive dyadic
scales fit below it. Global sufficiency requires the separate reduction proof. -/
def cutoff (m : Nat) : Nat := 3*2^(m+3)+m

theorem cutoff_pos (m : Nat) : 1≤cutoff m := by
  have h := Nat.two_pow_pos (m+3)
  dsimp [cutoff]
  omega

theorem representative_scale_large (m : Nat) : 2*m+2 < 2^(m+2) := by
  have h := ThueMorseBits.index_lt_two_pow m
  have hp : 2^(m+2)=4*2^m := by
    rw [show m+2=(m+1)+1 by omega,Nat.pow_succ,Nat.pow_succ]
    omega
  rw [hp]
  omega

theorem best_at_cutoff_ge_neg_one (s : Nat → Bool) (m : Nat)
    (hag : AgreeFrom s ThueMorseBits.t m) :
    -1 ≤ best s m (cutoff m-1) := by
  have large := representative_scale_large m
  obtain ⟨v,hv,hupper,_,hpath⟩ := sharp_tail_witness s m (m+2) hag (by omega)
  have hlen := (FiniteEditExact.height_isMaximum s m hag v).2 _ hpath
  have hp : 2^(m+3)=2*2^(m+2) := by
    rw [show m+3=(m+2)+1 by omega,Nat.pow_succ]
    omega
  have hn : v≤cutoff m := by dsimp [cutoff]; rw [hp]; omega
  have hc := cutoff_pos m
  have hbest := residual_le_best s m (cutoff m-1) v hv (by omega)
  dsimp [residual] at hbest
  have hpow := Nat.two_pow_pos (m+2)
  omega

end FiniteEditAlgorithm

#print axioms FiniteEditAlgorithm.best_attained
#print axioms FiniteEditAlgorithm.sharp_tail_witness
#print axioms FiniteEditAlgorithm.best_at_cutoff_ge_neg_one