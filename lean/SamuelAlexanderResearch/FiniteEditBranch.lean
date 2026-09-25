import SamuelAlexanderResearch.FullHeight
import SamuelAlexanderResearch.FiniteEditExact

/-! Long matching paths from a dyadic extremal start have a forced initial segment. This branch-separation theorem supports the exact individual finite-edit optimum. -/

namespace FiniteEditBranch

open ThueMorseBits SharpThueMorse FullHeight
open SamuelAlexanderResearch.ThueMorseBound
open BinaryAvoidance QuantitativeAvoidance FiniteEditStability

abbrev Y (T z k : Nat) := trajectory t (fun j => t (T+j)) z k

private theorem blockEq (n a b count i : Nat)
    (hc : ∀ j : Fin count, t (a+j.val) = t (b+j.val))
    (hi : i < count*2^n) : t (a*2^n+i) = t (b*2^n+i) :=
  block_eq n a b count i (fun j hj => hc ⟨j,hj⟩) hi

private theorem blockNe (n a b count i : Nat)
    (hc : ∀ j : Fin count, t (a+j.val) ≠ t (b+j.val))
    (hi : i < count*2^n) : t (a*2^n+i) ≠ t (b*2^n+i) :=
  block_ne n a b count i (fun j hj => hc ⟨j,hj⟩) hi

private theorem y_ones (T z k x len : Nat) (hs : Y T z k = x)
    (hb : ∀ i, i < len → t (x+i+1) = t (T+k+i)) :
    Y T z (k+len) = x+len := by
  apply run_ones t (fun j => t (T+j)) z k x len hs
  intro i hi
  simpa only [Nat.add_assoc] using hb i hi

private theorem y_twos (T z k x len : Nat) (hs : Y T z k = x)
    (hb : ∀ i, i < len → t (x+2*i+1) ≠ t (T+k+i)) :
    Y T z (k+len) = x+2*len := by
  apply run_twos t (fun j => t (T+j)) z k x len hs
  intro i hi
  simpa only [Nat.add_assoc] using hb i hi

private theorem y_translate_segment (T z k d v len : Nat)
    (hs : Y T z k = d + X v (T+k))
    (hb : ∀ j, j < len →
      t (d+X v (T+k+j)+1) = t (X v (T+k+j)+1)) :
    ∀ j, j ≤ len → Y T z (k+j) = d+X v (T+k+j) := by
  intro j hj
  induction j with
  | zero => simpa using hs
  | succ j ih =>
    have hp := ih (by omega)
    have hbit := hb j (by omega)
    change boundary t (t (T+(k+j))) (Y T z (k+j)) =
      d + boundary t (t (T+k+j)) (X v (T+k+j))
    rw [hp]
    have ht : T+(k+j)=T+k+j := by omega
    rw [ht]
    simp only [boundary]
    rw [hbit]
    split <;> omega

/-- The noncanonical midpoint boundary meets the original right boundary.
This is the only new substantive dyadic trajectory identity needed below. -/
theorem bad_boundary_join_large (n : Nat) :
    Y (4*2^n) (28*2^n) (28*2^n) = 80*2^n-1 := by
  let u := 2^n
  have hu : 0 < u := Nat.two_pow_pos n
  have hp1 : 2^(n+1)=2*u := by simp only [Nat.pow_succ]; dsimp [u]; omega
  have hp2 : 2^(n+2)=4*u := by
    rw [show n+2=(n+1)+1 by omega, Nat.pow_succ, hp1]
    omega
  change Y (4*u) (28*u) (28*u) = 80*u-1

  have h1raw := y_twos (4*u) (28*u) 0 (28*u) (2*u) rfl (by
    intro i hi
    have he : 28*u+2*i+1=2*(14*u+i)+1 := by omega
    rw [he, t_double_add_one]
    have hb := blockEq n 14 4 2 i (by decide +kernel) hi
    change t (14*u+i)=t (4*u+i) at hb
    rw [hb]
    simp)
  have h1 : Y (4*u) (28*u) (2*u)=32*u := by
    have he : 28*u+2*(2*u)=32*u := by omega
    simpa only [Nat.zero_add, he] using h1raw

  have h2 : Y (4*u) (28*u) (2*u+1)=32*u+1 := by
    change boundary t (t (4*u+2*u)) (Y (4*u) (28*u) (2*u)) = 32*u+1
    rw [h1]
    have he : 32*u+1=2*(16*u)+1 := by omega
    have ht : 4*u+2*u=6*u := by omega
    have hb : t (32*u+1)=t (6*u) := by
      rw [he, t_double_add_one]
      dsimp [u]
      rw [t_mul_two_pow, t_mul_two_pow]
      decide +kernel
    simp only [boundary, ht, if_pos hb]

  have h3raw := y_twos (4*u) (28*u) (2*u+1) (32*u+1) (4*u-1) h2 (by
    intro i hi
    have he : (32*u+1)+2*i+1=2*(16*u+(1+i)) := by omega
    have ht : 4*u+(2*u+1)+i=6*u+(1+i) := by omega
    rw [he, ht, t_double]
    exact blockNe n 16 6 4 (1+i) (by decide +kernel) (by omega))
  have h3 : Y (4*u) (28*u) (6*u)=40*u-1 := by
    have ht : 2*u+1+(4*u-1)=6*u := by omega
    have hx : 32*u+1+2*(4*u-1)=40*u-1 := by omega
    simpa only [ht,hx] using h3raw

  have h4raw := y_ones (4*u) (28*u) (6*u) (40*u-1) (2*u) h3 (by
    intro i hi
    have he : 40*u-1+i+1=40*u+i := by omega
    have ht : 4*u+6*u+i=10*u+i := by omega
    rw [he,ht]
    exact blockEq n 40 10 2 i (by decide +kernel) hi)
  have h4 : Y (4*u) (28*u) (8*u)=42*u-1 := by
    have ht : 6*u+2*u=8*u := by omega
    have hx : 40*u-1+2*u=42*u-1 := by omega
    simpa only [ht,hx] using h4raw

  have href0 : X (6*u) (8*u)=20*u-1 := five_run_join n
  have hrefInput : X (6*u) (16*u-4*2^(n+1)) =
      2*(16*u)-6*2^(n+1)-1 := by
    rw [hp1]
    have ht : 16*u-4*(2*u)=8*u := by omega
    have hx : 2*(16*u)-6*(2*u)-1=20*u-1 := by omega
    simpa only [ht,hx] using href0
  have hrefStartRaw := descent_block (n+1) 0 (6*u) (16*u)
    (by rw [hp1]; simp only [Nat.zero_add]; omega) hrefInput
  have hrefStart : X (6*u) (12*u)=26*u-1 := by
    rw [hp1] at hrefStartRaw
    have ht : 16*u-2*(2*u)=12*u := by omega
    have hx : 2*(16*u)-3*(2*u)-1=26*u-1 := by omega
    simpa only [ht,hx] using hrefStartRaw
  have hrefEndInput : X (6*u) (4*2^(n+1))=10*2^(n+1)-1 := by
    rw [hp1]
    have ht : 4*(2*u)=8*u := by omega
    have hx : 10*(2*u)-1=20*u-1 := by omega
    simpa only [ht,hx] using href0
  have hrefEndRaw := (common_descent (n+1) (6*u) hrefEndInput).2
  have hrefEnd : X (6*u) (16*u-2)=32*u-4 := by
    rw [hp1] at hrefEndRaw
    have ht : 8*(2*u)-2=16*u-2 := by omega
    rw [ht] at hrefEndRaw
    omega

  have htranslated := y_translate_segment (4*u) (28*u) (8*u)
    (16*u) (6*u) (4*u-2) (by
      have ht : 4*u+8*u=12*u := by omega
      rw [ht,hrefStart,h4]
      omega) (by
      intro j hj
      have ht : 4*u+8*u+j=12*u+j := by omega
      rw [ht]
      have hlo := time_mono (6*u) (12*u) (12*u+j) (by omega)
      have hhi := time_mono (6*u) (12*u+j) (16*u-2) (by omega)
      rw [hrefStart] at hlo
      rw [hrefEnd] at hhi
      let i := X (6*u) (12*u+j)+1-24*u
      have he : X (6*u) (12*u+j)+1=24*u+i := by dsimp [i]; omega
      have he' : 16*u+X (6*u) (12*u+j)+1=40*u+i := by dsimp [i]; omega
      rw [he',he]
      exact blockEq n 40 24 8 i (by decide +kernel) (by dsimp [i]; omega))
    (4*u-2) (Nat.le_refl _)
  have h5 : Y (4*u) (28*u) (12*u-2)=48*u-4 := by
    have ht : 8*u+(4*u-2)=12*u-2 := by omega
    have ht' : 4*u+8*u+(4*u-2)=16*u-2 := by omega
    rw [ht,ht',hrefEnd] at htranslated
    omega

  have hbitA : t (48*u-3) ≠ t (16*u-2) := by
    have he : 48*u-3=4*(12*u-1)+1 := by omega
    have ht : 16*u-2=2*(8*u-1) := by omega
    rw [he,t_four_mul_one,ht,t_double]
    have hb := blockEq (n+2) 2 1 1 (4*u-1) (by decide +kernel) (by rw [hp2]; omega)
    rw [hp2] at hb
    have hleft : 2*(4*u)+(4*u-1)=12*u-1 := by omega
    have hright : 1*(4*u)+(4*u-1)=8*u-1 := by omega
    rw [hleft,hright] at hb
    rw [hb]
    simp
  have hbitB : t (48*u-1) ≠ t (16*u-1) := by
    have hb := blockNe n 47 15 1 (u-1) (by decide +kernel) (by omega)
    have he : 47*u+(u-1)=48*u-1 := by omega
    have ht : 15*u+(u-1)=16*u-1 := by omega
    change t (47*u+(u-1)) ≠ t (15*u+(u-1)) at hb
    simpa only [he,ht] using hb
  have h6raw := y_twos (4*u) (28*u) (12*u-2) (48*u-4) 2 h5 (by
    intro i hi
    have hc : i=0 ∨ i=1 := by omega
    rcases hc with hc | hc <;> subst i
    · have he : 48*u-4+2*0+1=48*u-3 := by omega
      have ht : 4*u+(12*u-2)+0=16*u-2 := by omega
      simpa only [he,ht] using hbitA
    · have he : 48*u-4+2*1+1=48*u-1 := by omega
      have ht : 4*u+(12*u-2)+1=16*u-1 := by omega
      simpa only [he,ht] using hbitB)
  have h6 : Y (4*u) (28*u) (12*u)=48*u := by
    have ht : 12*u-2+2=12*u := by omega
    have hx : 48*u-4+2*2=48*u := by omega
    simpa only [ht,hx] using h6raw
  have h7 : Y (4*u) (28*u) (12*u+1)=48*u+1 := by
    change boundary t (t (4*u+12*u)) (Y (4*u) (28*u) (12*u))=48*u+1
    rw [h6]
    have ht : 4*u+12*u=16*u := by omega
    have he : 48*u+1=2*(24*u)+1 := by omega
    have hb : t (48*u+1)=t (16*u) := by
      rw [he,t_double_add_one]
      dsimp [u]
      rw [t_mul_two_pow,t_mul_two_pow]
      decide +kernel
    simp only [boundary,ht,if_pos hb]
  have h8raw := y_twos (4*u) (28*u) (12*u+1) (48*u+1) (4*u-1) h7 (by
    intro i hi
    have he : 48*u+1+2*i+1=2*(24*u+(1+i)) := by omega
    have ht : 4*u+(12*u+1)+i=16*u+(1+i) := by omega
    rw [he,ht,t_double]
    exact blockNe n 24 16 4 (1+i) (by decide +kernel) (by omega))
  have h8 : Y (4*u) (28*u) (16*u)=56*u-1 := by
    have ht : 12*u+1+(4*u-1)=16*u := by omega
    have hx : 48*u+1+2*(4*u-1)=56*u-1 := by omega
    simpa only [ht,hx] using h8raw
  have h9raw := y_twos (4*u) (28*u) (16*u) (56*u-1) (12*u) h8 (by
    intro i hi
    have he : 56*u-1+2*i+1=2*(28*u+i) := by omega
    have ht : 4*u+16*u+i=20*u+i := by omega
    rw [he,ht,t_double]
    have hb := blockNe (n+2) 7 5 3 i (by decide +kernel) (by rw [hp2]; omega)
    rw [hp2] at hb
    have hleft : 7*(4*u)=28*u := by omega
    have hright : 5*(4*u)=20*u := by omega
    simpa only [hleft,hright] using hb)
  have ht : 16*u+12*u=28*u := by omega
  have hx : 56*u-1+2*(12*u)=80*u-1 := by omega
  simpa only [ht,hx] using h9raw

theorem bad_boundary_join (n : Nat) :
    Y (2^n) (7*2^n) (7*2^n)=20*2^n-1 := by
  cases n with
  | zero => decide +kernel
  | succ n =>
    cases n with
    | zero => decide +kernel
    | succ n =>
      have hp : 2^(n+1+1)=4*2^n := by
        rw [Nat.pow_succ,Nat.pow_succ]
        omega
      rw [hp]
      have h := bad_boundary_join_large n
      have h7 : 7*(4*2^n)=28*2^n := by omega
      have h20 : 20*(4*2^n)=80*2^n := by omega
      simpa only [h7,h20] using h

private theorem edge_boundary_lower {u w : Nat} {label : Bool}
    (he : BinaryAvoidance.Edge t u w label) : boundary t label u ≤ w := by
  rcases he with ⟨_, ⟨hw,hb⟩ | ⟨hw,hb⟩⟩
  · rw [binary_row_eq] at hb
    subst w
    simp [boundary,hb]
  · have h := boundary_bounds t label u
    omega

theorem path_above_y (path : Nat → Nat) (ell T z : Nat)
    (hm : MatchesPrefix t path ell) (hT : T ≤ ell) (hz : z ≤ path T) :
    ∀ j, T+j ≤ ell → Y T z j ≤ path (T+j) := by
  intro j hj
  induction j with
  | zero =>
    change z ≤ path (T+0)
    simpa using hz
  | succ j ih =>
    have hp := ih (by omega)
    have he := hm (T+j) (by omega)
    have hb := edge_boundary_lower he
    have hmono := boundary_mono t (t (T+j)) hp
    change boundary t (t (T+j)) (Y T z j) ≤ path (T+(j+1))
    have ht : T+(j+1)=T+j+1 := by omega
    rw [ht]
    omega

/-- Every sufficiently long actual extremal path has the forced midpoint. -/
theorem long_extremal_midpoint (n : Nat) (path : Nat → Nat) (ell : Nat)
    (hs : path 0=6*2^n-1) (hm : MatchesPrefix t path ell)
    (hlen : 8*2^n ≤ ell) : path (2^n)=7*2^n-1 := by
  let r := 2^n
  have hr : 0<r := Nat.two_pow_pos n
  have hlo := (prefix_displacement t path ell hm r (by omega)).1
  change path r=7*r-1
  by_cases hn : path r=7*r-1
  · exact hn
  have hbad : 7*r ≤ path r := by dsimp [r] at *; omega
  have hb := path_above_y path ell r (7*r) hm (by omega) hbad (7*r) (by omega)
  have ht : r+7*r=8*r := by omega
  rw [ht] at hb
  have hj := bad_boundary_join n
  change Y r (7*r) (7*r)=20*r-1 at hj
  rw [hj] at hb
  have hp := binary_prefix_reachable path (8*r) (fun k hk => hm k (by omega))
  have hp' := (reachable_iff_interval t t (path 0) (by dsimp [r] at *; omega)
    (8*r) (path (8*r))).mp hp
  have hs' : path 0+1=6*r := by dsimp [r] at *; omega
  rw [hs'] at hp'
  have hrEnd := five_run_join n
  change X (6*r) (8*r)=20*r-1 at hrEnd
  change X (path 0) (8*r) ≤ path (8*r) ∧ path (8*r)<X (6*r) (8*r) at hp'
  rw [hrEnd] at hp'
  omega

theorem prefix_lower_between (path : Nat → Nat) (ell i j : Nat)
    (hm : MatchesPrefix t path ell) (hij : i ≤ j) (hj : j ≤ ell) :
    path i+(j-i) ≤ path j := by
  induction j with
  | zero =>
    have hi : i=0 := by omega
    subst i
    simp
  | succ j ih =>
    by_cases hi : i ≤ j
    · have hp := ih hi (by omega)
      have he := edge_displacement t (path j) (path (j+1)) (t j) (hm j (by omega))
      omega
    · have hi' : i=j+1 := by omega
      subst i
      simp

/-- The precise branch-separation statement needed for the finite reduction. -/
theorem branch_separation (n m : Nat) (path : Nat → Nat) (ell : Nat)
    (hmq : 2*m ≤ 2^n) (hs : path 0=3*2^n-1)
    (hm : MatchesPrefix t path ell) (hlen : 4*2^n ≤ ell) :
    path m=3*2^n+m-1 := by
  cases n with
  | zero =>
    have hzero : m=0 := by
      have h : 2*m ≤ 1 := by simpa using hmq
      omega
    subst m
    simpa using hs
  | succ n =>
    have hp : 2^(n+1)=2*2^n := by rw [Nat.pow_succ]; omega
    have hs' : path 0=6*2^n-1 := by rw [hp] at hs; omega
    have hlen' : 8*2^n ≤ ell := by rw [hp] at hlen; omega
    have mid := long_extremal_midpoint n path ell hs' hm hlen'
    have hmr : m ≤ 2^n := by rw [hp] at hmq; omega
    have hlo := (prefix_displacement t path ell hm m (by omega)).1
    have hhi := prefix_lower_between path ell m (2^n) hm hmr (by omega)
    rw [hp]
    omega

end FiniteEditBranch

#print axioms FiniteEditBranch.bad_boundary_join
#print axioms FiniteEditBranch.branch_separation