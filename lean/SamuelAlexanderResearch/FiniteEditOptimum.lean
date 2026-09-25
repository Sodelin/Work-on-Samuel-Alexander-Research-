import SamuelAlexanderResearch.FiniteEditBranch
import SamuelAlexanderResearch.FiniteEditGap
import SamuelAlexanderResearch.FiniteEditAlgorithm
import SamuelAlexanderResearch.ThueMorseWindow

/-! A computable global cutoff for the exact individual finite-edit additive constant. Every fixed target agreeing with Thue-Morse from m onward has an attained optimum found by the finite procedure below. -/
namespace FiniteEditOptimum

open BinaryAvoidance QuantitativeAvoidance FiniteEditStability
open PhaseShift PhaseHeight FiniteEditAlgorithm

theorem local_window_translation (m n N w : Nat)
    (hn : 2*m+2<2^n) (hN : 2*m+2<2^N) (hpar : n%2=N%2)
    (hlo : 3*2^n ≤ w+m+1) (hhi : w≤3*2^n+2*m+1) :
    ThueMorseBits.t (w+3*2^N-3*2^n)=ThueMorseBits.t w := by
  by_cases hr : 3*2^n≤w
  · let d := w-3*2^n
    have hw : w=3*2^n+d := by dsimp [d]; omega
    have hw' : w+3*2^N-3*2^n=3*2^N+d := by dsimp [d]; omega
    rw [hw',hw]
    exact ThueMorseWindow.same_right_window N n d (by dsimp [d]; omega)
      (by dsimp [d]; omega)
  · let r := 3*2^n-w
    have hw : w=3*2^n-r := by dsimp [r]; omega
    have hw' : w+3*2^N-3*2^n=3*2^N-r := by dsimp [r]; omega
    rw [hw',hw]
    exact ThueMorseWindow.same_parity_left_window N n r
      (by dsimp [r]; omega) (by dsimp [r]; omega)
      (by dsimp [r]; omega) hpar.symm

theorem row_window_translation (s : Nat → Bool) (m n N w : Nat)
    (hag : AgreeFrom s ThueMorseBits.t m)
    (hn : 2*m+2<2^n) (hN : 2*m+2<2^N) (hpar : n%2=N%2)
    (hlo : 3*2^n≤w+m+1) (hhi : w≤3*2^n+2*m+1) :
    row s (w+3*2^N-3*2^n)=row s w := by
  rw [row_eq_of_agree s ThueMorseBits.t m hag _ (by omega),
    row_eq_of_agree s ThueMorseBits.t m hag _ (by omega),
    SharpThueMorse.binary_row_eq,SharpThueMorse.binary_row_eq]
  exact local_window_translation m n N w hn hN hpar hlo hhi

theorem relocate_edge (s : Nat → Bool) (m n N u w : Nat) (label : Bool)
    (hag : AgreeFrom s ThueMorseBits.t m)
    (hn : 2*m+2<2^n) (hN : 2*m+2<2^N) (hpar : n%2=N%2)
    (hlo : 3*2^n≤u+m+1) (hhi : w≤3*2^n+2*m+1)
    (edge : Edge s u w label) :
    Edge s (u+3*2^N-3*2^n) (w+3*2^N-3*2^n) label := by
  have hdisp := edge_displacement s u w label edge
  have hrow := row_window_translation s m n N w hag hn hN hpar (by omega) hhi
  rcases edge with ⟨_,one | two⟩
  · refine ⟨by omega,Or.inl ⟨by omega,?_⟩⟩
    rw [hrow]
    exact one.2
  · refine ⟨by omega,Or.inr ⟨by omega,?_⟩⟩
    rw [hrow]
    exact two.2

/-- Relocate the finite edited prefix to a same-parity dyadic scale, then
append the already proved extremal shifted suffix. -/
theorem relocate_canonical_prefix (s : Nat → Bool) (m n N : Nat)
    (hag : AgreeFrom s ThueMorseBits.t m)
    (hn : 2*m+2<2^n) (hN : 2*m+2<2^N) (hpar : n%2=N%2)
    (path : Nat → Nat) (ell : Nat) (hm : MatchesPrefix s path ell)
    (hlen : m≤ell) (hcut : path m=3*2^n+m-1) :
    ∃ v, 1≤v ∧ v≤3*2^N-1 ∧
      v+3*2^n=path 0+3*2^N ∧ HasPrefix s v (8*2^N-3) := by
  have hdisp := prefix_displacement s path ell hm m hlen
  let translated := fun k => path k+3*2^N-3*2^n
  have hv : 1≤translated 0 := by dsimp [translated]; omega
  have hbound : translated 0≤3*2^N-1 := by dsimp [translated]; omega
  have hstart : translated 0+3*2^n=path 0+3*2^N := by dsimp [translated]; omega
  have hend : translated m=3*2^N+m-1 := by dsimp [translated]; omega
  have hprefix : MatchesPrefix s translated m := by
    intro k hk
    have hlo := prefix_displacement s path ell hm k (by omega)
    have hhi := prefix_displacement s path ell hm (k+1) (by omega)
    exact relocate_edge s m n N (path k) (path (k+1)) (s k) hag hn hN hpar
      (by omega) (by omega) (hm k (by omega))
  have front : 3*2^N+m-1 ∈ frontier s (translated 0) m :=
    (mem_frontier s (translated 0) m _).mpr ⟨translated,rfl,hend,hprefix⟩
  have tail : HasPrefix (shift ThueMorseBits.t m)
      ((3*2^N+m-1)-2*m) (8*2^N-m-3) := by
    have hi : (3*2^N+m-1)-2*m=3*2^N-m-1 := by omega
    rw [hi]
    exact PhaseExtremal.shifted_family_prefix N m (by omega)
  have whole := (FiniteEditExact.prefix_decomposition s ThueMorseBits.t m hag
    (translated 0) (8*2^N-m-3)).mpr ⟨_,front,tail⟩
  have he : m+(8*2^N-m-3)=8*2^N-3 := by omega
  rw [he] at whole
  exact ⟨translated 0,hv,hbound,hstart,whole⟩

theorem representative (m n : Nat) :
    ∃ N, (N=m+2 ∨ N=m+3) ∧ n%2=N%2 := by
  by_cases h : n%2=(m+2)%2
  · exact ⟨m+2,Or.inl rfl,h⟩
  · exact ⟨m+3,Or.inr rfl,by omega⟩

theorem cutoff_large (m : Nat) : 7*m+8≤cutoff m := by
  have hl := representative_scale_large m
  have hp : 2^(m+3)=2*2^(m+2) := by
    rw [show m+3=(m+2)+1 by omega,Nat.pow_succ]
    omega
  dsimp [cutoff]
  rw [hp]
  omega

/-- The all-start reduction. The cutoff is computable and independent of the
edited bit values, while every height in the finite maximum is exact. -/
theorem residual_le_finite_best (s : Nat → Bool) (m : Nat)
    (hag : AgreeFrom s ThueMorseBits.t m) (v : Nat) (hv : 1≤v) :
    residual s m v≤best s m (cutoff m-1) := by
  have hc := cutoff_pos m
  by_cases hsmall : v≤cutoff m
  · exact residual_le_best s m (cutoff m-1) v hv (by omega)
  · by_cases hdone : residual s m v≤best s m (cutoff m-1)
    · exact hdone
    have hnonneg := best_at_cutoff_ge_neg_one s m hag
    have hlargeCut := cutoff_large m
    let ell := FiniteEditExact.height s m v
    have hres : 8*v≤3*ell := by dsimp [residual,ell] at *; omega
    obtain ⟨path,hzero,hm⟩ := (FiniteEditExact.height_isMaximum s m hag v).1
    have hm' : MatchesPrefix s path ell := hm
    obtain ⟨changed,hchanged,hup,hlo,hsame⟩ :=
      finite_edit_transport s ThueMorseBits.t m hag path ell hm'
    have hlen : ell≤FullHeight.height (changed 0) :=
      (FullHeight.height_isMaximum (changed 0)).2 ell ⟨changed,rfl,hchanged⟩
    rcases FiniteEditGap.off_extremal_gap (changed 0) with ⟨n,ha⟩ | hgap
    · have hn : 2*m+2<2^n := by omega
      have hfour : 4*2^n≤ell := by omega
      have hbranch := FiniteEditBranch.branch_separation n m changed ell
        (by omega) ha hchanged hfour
      have hsame' := hsame m (Nat.min_le_left m ell)
      have hcut : path m=3*2^n+m-1 := by omega
      have hlength : ell≤8*2^n-3 := by
        have hp := Nat.two_pow_pos n
        have hsharp := SharpThueMorse.binary_path_prefix_bound changed ell
          (by omega) hchanged
        omega
      obtain ⟨N,hNcase,hpar⟩ := representative m n
      have hpow : 2^(m+3)=2*2^(m+2) := by
        rw [show m+3=(m+2)+1 by omega,Nat.pow_succ]
        omega
      have hNlarge : 2*m+2<2^N := by
        rcases hNcase with hNcase | hNcase <;> rw [hNcase]
        · exact representative_scale_large m
        · have h := representative_scale_large m
          rw [hpow]
          omega
      have hNbound : 2^N≤2^(m+3) := by
        rcases hNcase with hNcase | hNcase <;> rw [hNcase]
        · rw [hpow]; omega
        · omega
      obtain ⟨v',hv',hbound',heq,hpath'⟩ :=
        relocate_canonical_prefix s m n N hag hn hNlarge hpar path ell hm' (by omega) hcut
      have hwithin : v'≤cutoff m := by dsimp [cutoff]; omega
      have hbest := residual_le_best s m (cutoff m-1) v' hv' (by omega)
      have hattain := (FiniteEditExact.height_isMaximum s m hag v').2 _ hpath'
      have hq := Nat.two_pow_pos n
      have hQ := Nat.two_pow_pos N
      dsimp [residual] at hbest hdone
      dsimp [ell] at hlength
      omega
    · have hshort : ell≤changed 0+1 := Nat.le_trans hlen hgap
      omega

/-- The executable finite maximum is attained as the genuine global optimum. -/
theorem individual_optimum_attained (s : Nat → Bool) (m : Nat)
    (hag : AgreeFrom s ThueMorseBits.t m) :
    (∀ v, 1≤v → residual s m v≤best s m (cutoff m-1)) ∧
    ∃ v, 1≤v ∧ v≤cutoff m ∧ residual s m v=best s m (cutoff m-1) := by
  refine ⟨fun v hv => residual_le_finite_best s m hag v hv,?_⟩
  obtain ⟨v,hv,hn,he⟩ := best_attained s m (cutoff m-1)
  have hc := cutoff_pos m
  exact ⟨v,hv,by omega,he⟩

/-- Exact smallest integer additive constant for this individual edited word. -/
theorem individual_additive_constant_iff (s : Nat → Bool) (m : Nat)
    (hag : AgreeFrom s ThueMorseBits.t m) (B : Int) :
    (∀ v len, 1≤v → IsMaximumPrefix s v len →
      3*(len : Int)≤8*(v : Int)+B) ↔ best s m (cutoff m-1)≤B := by
  constructor
  · intro h
    obtain ⟨v,hv,_,he⟩ := (individual_optimum_attained s m hag).2
    have hb := h v (FiniteEditExact.height s m v) hv
      (FiniteEditExact.height_isMaximum s m hag v)
    dsimp [residual] at he
    omega
  · intro h v len hv hmax
    have bound := residual_le_finite_best s m hag v hv
    have he := (FiniteEditExact.maximum_iff_height s m hag v len).mp hmax
    dsimp [residual] at bound
    omega

end FiniteEditOptimum
#print axioms FiniteEditOptimum.residual_le_finite_best
#print axioms FiniteEditOptimum.individual_optimum_attained
#print axioms FiniteEditOptimum.individual_additive_constant_iff