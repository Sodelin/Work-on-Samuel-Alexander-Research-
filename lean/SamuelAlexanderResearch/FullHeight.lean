import SamuelAlexanderResearch.FiniteEditStability

/-! Exact matching heights for the actual Thue--Morse population. -/
namespace FullHeight
open ThueMorseBits SharpThueMorse FiniteEditStability
open SamuelAlexanderResearch.ThueMorseBound
open QuantitativeAvoidance

def bit (b : Bool) : Nat := if b then 1 else 0

def special (h : Nat) : Bool :=
  (h % 4 == 1) && !(t (h / 4)) && t (h / 4 + 1)

def evenValue (h r : Nat) : Nat :=
  if t h then 1 - r % 2
  else if r = 1 then 7 - 2 * bit (t (h+1))
  else (4 - 2 * bit (t (h+1))) * 2^r - 1

def oddValue (h r : Nat) : Nat :=
  if t h then
    if t (h+1) then
      if special h then 16 * 2^r - 3 else 10 * 2^r - 1
    else 4 * 2^r - 1
  else 0

def FormulaSpec (H : Nat → Nat) : Prop :=
  H 0 = 1 ∧ ∀ h r,
    H ((4*h+2)*2^r-2) = evenValue h r ∧
    H ((4*h+2)*2^r-1) = oddValue h r

private theorem actual_maximum_exists (v : Nat) :
    ∃ ell, IsMaximumPrefix t v ell := by
  cases v with
  | zero =>
    refine ⟨1, thue_zero_maximum.1, ?_⟩
    intro len ⟨path, hz, hm⟩
    exact thue_zero_maximum.2 path len hz hm
  | succ v =>
    obtain ⟨ell, hm, _⟩ := finite_edit_thue_maximum t 0 (fun _ _ => rfl)
      (v+1) (by omega)
    exact ⟨ell, hm⟩

/-- The attained maximum over actual finite matching paths, including start zero. -/
noncomputable def height (v : Nat) : Nat := Classical.choose (actual_maximum_exists v)

theorem height_isMaximum (v : Nat) : IsMaximumPrefix t v (height v) :=
  Classical.choose_spec (actual_maximum_exists v)

theorem height_eq_of_maximum (v ell : Nat) (hm : IsMaximumPrefix t v ell) :
    height v = ell := by
  have h := height_isMaximum v
  exact Nat.le_antisymm (hm.2 _ h.1) (h.2 _ hm.1)

theorem height_zero : height 0 = 1 := by
  apply height_eq_of_maximum
  refine ⟨thue_zero_maximum.1, ?_⟩
  intro len ⟨path, hz, hm⟩
  exact thue_zero_maximum.2 path len hz hm

theorem height_eq_of_boundaries (v ell : Nat) (hv : 1 ≤ v)
    (hsep : X v ell < X (v+1) ell)
    (hjoin : X v (ell+1) = X (v+1) (ell+1)) : height v = ell := by
  have hm := (maximum_length_iff t t v ell hv).2 ⟨hsep, hjoin⟩
  apply height_eq_of_maximum
  obtain ⟨w, hw⟩ := hm.1
  obtain ⟨path, hz, _, hp⟩ := reachable_thue_prefix v ell w hw
  refine ⟨⟨path, hz, hp⟩, ?_⟩
  intro len ⟨path, hz, hp⟩
  by_cases hn : len ≤ ell
  · exact hn
  · have short : MatchesPrefix t path (ell+1) := fun k hk => hp k (by omega)
    have hr := binary_prefix_reachable path (ell+1) short
    rw [hz] at hr
    exact False.elim (hm.2 ⟨path (ell+1), hr⟩)

theorem time_mono (v k j : Nat) (h : k ≤ j) : X v k ≤ X v j := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => simp
  | succ d ih =>
    have hb := boundary_bounds t (t (k+d)) (X v (k+d))
    change X v k ≤ boundary t (t (k+d)) (X v (k+d))
    omega

/-- A finite color-window agreement transports a whole boundary trajectory. -/
theorem window_translate (d v lo hi K : Nat)
    (hlo : lo ≤ v+1) (hhi : X v K < hi)
    (hbits : ∀ w, lo ≤ w → w < hi → t (d+w) = t w) :
    ∀ k, k ≤ K → X (d+v) k = d + X v k := by
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
    have hp := ih (by omega)
    have hb := boundary_bounds t (t k) (X v k)
    have hstart := trajectory_ge_start t t v k
    change v ≤ X v k at hstart
    have hend := time_mono v (k+1) K hk
    have hc := hbits (X v k+1) (by omega) (by
      change boundary t (t k) (X v k) ≤ X v K at hend
      omega)
    change boundary t (t k) (X (d+v) k) = d + boundary t (t k) (X v k)
    rw [hp]
    simp only [boundary, Nat.add_assoc, hc]
    split <;> omega

@[simp] theorem t_four_mul (h : Nat) : t (4*h) = t h := by
  rw [show 4*h = 2*(2*h) by omega, t_double, t_double]
@[simp] theorem t_four_mul_one (h : Nat) : t (4*h+1) = !(t h) := by
  rw [show 4*h+1 = 2*(2*h)+1 by omega, t_double_add_one, t_double]
@[simp] theorem t_four_mul_two (h : Nat) : t (4*h+2) = !(t h) := by
  rw [show 4*h+2 = 2*(2*h+1) by omega, t_double, t_double_add_one]
@[simp] theorem t_four_mul_three (h : Nat) : t (4*h+3) = t h := by
  rw [show 4*h+3 = 2*(2*h+1)+1 by omega, t_double_add_one, t_double_add_one]
  simp

theorem t_even_mul_pow_one (a r : Nat) : t ((2*a)*2^r+1) = !(t a) := by
  cases r with
  | zero => simpa using t_double_add_one a
  | succ r =>
    have hp : 1 < 2^(r+1) := by rw [Nat.pow_succ]; have := Nat.two_pow_pos r; omega
    rw [t_dyadic_block _ _ _ hp, t_double]
    cases t a <;> simp

theorem power_last (r : Nat) : t (2^r-1) = (r % 2 == 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hp := Nat.two_pow_pos r
    rw [show 2^(r+1)-1 = 2*(2^r-1)+1 by rw [Nat.pow_succ]; omega,
      t_double_add_one, ih]
    have hm := Nat.mod_lt r (by decide : 0 < 2)
    by_cases hr : r % 2 = 0
    · simp [hr, show (r+1)%2=1 by omega]
    · simp [show r%2=1 by omega, show (r+1)%2=0 by omega]

theorem t_z (h r : Nat) : t ((4*h+2)*2^r) = !(t h) := by
  rw [t_mul_two_pow, t_four_mul_two]

theorem t_z_one (h r : Nat) : t ((4*h+2)*2^r+1) = t h := by
  have he : 4*h+2 = 2*(2*h+1) := by omega
  rw [he, t_even_mul_pow_one, t_double_add_one]
  simp

theorem t_z_last (h r : Nat) :
    t ((4*h+2)*2^r-1) = Bool.xor (!(t h)) (r%2 == 1) := by
  have hp := Nat.two_pow_pos r
  have he : (4*h+2)*2^r-1 = (4*h+1)*2^r+(2^r-1) := by
    simp only [Nat.add_mul]
    omega
  rw [he, t_dyadic_block _ _ _ (by omega), t_four_mul_one, power_last]

theorem odd_false (h r : Nat) (hh : t h = false) :
    height ((4*h+2)*2^r-1) = 0 := by
  have hp := Nat.two_pow_pos r
  have hz : 2 ≤ (4*h+2)*2^r := by
    have := Nat.mul_le_mul_right (2^r) (show 2 ≤ 4*h+2 by omega)
    omega
  apply height_eq_of_boundaries _ 0 (by omega)
  · simp [X, trajectory]
  · have he : (4*h+2)*2^r-1+1 = (4*h+2)*2^r := by omega
    simp only [X, trajectory, boundary, t_zero, he, t_z, t_z_one, hh,
      Bool.not_false, Bool.true_eq_false, ↓reduceIte]
    omega

theorem even_true (h r : Nat) (hh : t h = true) :
    height ((4*h+2)*2^r-2) = 1-r%2 := by
  have hp := Nat.two_pow_pos r
  have hhpos : 1 ≤ h := by
    by_cases hn : h=0
    · simp [hn] at hh
    · omega
  have hz : 6 ≤ (4*h+2)*2^r := by
    have := Nat.mul_le_mul_right (2^r) (show 6 ≤ 4*h+2 by omega)
    omega
  have he : (4*h+2)*2^r-2+1 = (4*h+2)*2^r-1 := by omega
  have hf : (4*h+2)*2^r-1+1 = (4*h+2)*2^r := by omega
  have hm := Nat.mod_lt r (by decide : 0 < 2)
  by_cases hr : r%2=0
  · have hb : t ((4*h+2)*2^r-1) = false := by rw [t_z_last, hh]; simp [hr]
    rw [hr]
    apply height_eq_of_boundaries _ 1 (by omega)
    · simp [X, trajectory, boundary, he, hf, t_z, hh, hb]
      omega
    · simp only [X, trajectory, boundary, he, hf, t_zero, t_one, t_z, t_z_one,
        hh, hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      omega
  · have hr : r%2=1 := by omega
    have hb : t ((4*h+2)*2^r-1) = true := by rw [t_z_last, hh]; simp [hr]
    rw [hr]
    apply height_eq_of_boundaries _ 0 (by omega)
    · simp [X, trajectory]
    · simp only [X, trajectory, boundary, he, hf, t_zero, t_z, hh, hb,
        Bool.not_true, Bool.true_eq_false, ↓reduceIte]
      omega

theorem run_ones_last (v k x len : Nat) (hlen : 0 < len)
    (hstart : X v k = x) (hbits : ∀ i, i < len → t (x+i+1) = t (k+i)) :
    X v (k+len)=x+len ∧ X v (k+len-1)=x+len-1 := by
  constructor
  · exact run_ones t t v k x len hstart hbits
  · have he := run_ones t t v k x (len-1) hstart (fun i hi => hbits i (by omega))
    simpa [show k+(len-1)=k+len-1 by omega, show x+(len-1)=x+len-1 by omega] using he

theorem run_twos_last (v k x len : Nat) (hlen : 0 < len)
    (hstart : X v k = x) (hbits : ∀ i, i < len → t (x+2*i+1) ≠ t (k+i)) :
    X v (k+len)=x+2*len ∧ X v (k+len-1)=x+2*len-2 := by
  constructor
  · exact run_twos t t v k x len hstart hbits
  · have he := run_twos t t v k x (len-1) hstart (fun i hi => hbits i (by omega))
    simpa [show k+(len-1)=k+len-1 by omega,
      show x+2*(len-1)=x+2*len-2 by omega] using he

theorem even_scale_one (h : Nat) (hh : t h=false) :
    height (4*h) = 3-2*bit (t (h+1)) := by
  by_cases hz : h=0
  · simp [hz, bit, height_zero]
  · have hb1 : t (4*h+1)=true := by simp [hh]
    have hb2 : t (4*h+2)=true := by simp [hh]
    have hb3 : t (4*h+3)=false := by simp [hh]
    have hb4 : t (4*h+4)=t (h+1) := by rw [show 4*h+4=4*(h+1) by omega]; simp
    have hb5 : t (4*h+5)=!(t (h+1)) := by rw [show 4*h+5=4*(h+1)+1 by omega]; simp
    have hb6 : t (4*h+6)=!(t (h+1)) := by rw [show 4*h+6=4*(h+1)+2 by omega]; simp
    have hb7 : t (4*h+7)=t (h+1) := by rw [show 4*h+7=4*(h+1)+3 by omega]; simp
    cases hu : t (h+1) with
    | false =>
      simp only [bit, Bool.false_eq_true, ↓reduceIte, Nat.mul_zero, Nat.sub_zero]
      apply height_eq_of_boundaries _ 3 (by omega)
      · simp [X, trajectory, boundary, Nat.add_assoc, hh, hb4, hb5, hb6, hu]
      · simp [X, trajectory, boundary, Nat.add_assoc, hh, hb4, hb5, hb6, hb7, hu]
    | true =>
      simp only [bit, ↓reduceIte]
      apply height_eq_of_boundaries _ 1 (by omega)
      · simp [X, trajectory, boundary, Nat.add_assoc, hh]
      · simp [X, trajectory, boundary, Nat.add_assoc, hh, hb4, hu]

/-- The two explicit run patterns for the odd branch with high bits `10`. -/
theorem odd_true_false (h r : Nat) (hh : t h=true) (hu : t (h+1)=false) :
    height ((4*h+2)*2^r-1) = 4*2^r-1 := by
  let q := 2^r
  let z := (4*h+2)*q
  have hp : 0<q := Nat.two_pow_pos r
  have hz : z = 4*(h*q)+2*q := by simp [z, Nat.add_mul, Nat.mul_assoc]
  have hzpos : 2 ≤ z := by omega
  have hleft := run_ones t t (z-1) 0 (z-1) (2*q) rfl (by
    intro i hi
    have he : z-1+i+1 = (4*h+2)*2^r+i := by change z-1+i+1=z+i; omega
    rw [he]
    have hb := block_eq r (4*h+2) 0 2 i (by
      intro j hj
      have hj : j=0 ∨ j=1 := by omega
      rcases hj with rfl | rfl <;> simp [hh, Nat.add_assoc]) hi
    simpa using hb)
  have hl : X (z-1) (2*q) = z+2*q-1 := by simpa [show z-1+2*q=z+2*q-1 by omega] using hleft
  have hleftlast := run_twos_last (z-1) (2*q) (z+2*q-1) (2*q) (by omega) hl (by
    intro i hi
    have he : z+2*q-1+2*i+1 = 2*((2*h+2)*2^r+i) := by
      simp only [Nat.add_mul, Nat.mul_assoc]
      change z+2*q-1+2*i+1=2*(2*(h*q)+2*q+i)
      omega
    rw [he, t_double]
    exact block_ne r (2*h+2) 2 2 i (by
      intro j hj
      have hj : j=0 ∨ j=1 := by omega
      rcases hj with rfl | rfl
      · rw [show 2*h+2+0=2*(h+1) by omega, t_double]; simp [hu]
      · rw [show 2*h+2+1=2*(h+1)+1 by omega, t_double_add_one]; simp [hu]) hi)
  have hright := run_twos t t z 0 z q rfl (by
    intro i hi
    have he : z+2*i+1=2*((2*h+1)*2^r+i)+1 := by
      simp only [Nat.add_mul, Nat.mul_assoc, Nat.one_mul]
      change z+2*i+1=2*(2*(h*q)+q+i)+1
      omega
    rw [he, t_double_add_one, t_dyadic_block _ r i hi, t_double_add_one, hh]
    simp)
  have hr : X z q=z+2*q := by simpa using hright
  have hr1 : X z (q+1)=z+2*q+1 := by
    change boundary t (t q) (X z q)=z+2*q+1
    rw [hr]
    have hb : t (z+2*q+1)=true := by
      have he : z+2*q+1=(2*(2*(h+1)))*2^r+1 := by
        simp only [Nat.add_mul, Nat.mul_assoc, Nat.one_mul]
        change z+2*q+1=2*(2*(h*q+q))+1
        omega
      rw [he, t_even_mul_pow_one, t_double, hu]
      rfl
    simp [boundary, hb, q]
  have hr2raw := run_twos t t z (q+1) (z+2*q+1) (q-1) hr1 (by
    intro i hi
    have hb : 1+i < 2^r := by change 1+i<q; omega
    have he : z+2*q+1+2*i+1=2*((2*h+2)*2^r+(1+i)) := by
      simp only [Nat.add_mul, Nat.mul_assoc]
      change z+2*q+1+2*i+1=2*(2*(h*q)+2*q+(1+i))
      omega
    have hk : q+1+i=1*2^r+(1+i) := by change q+1+i=1*q+(1+i); omega
    rw [he, hk, t_double, t_dyadic_block _ _ _ hb, t_dyadic_block _ _ _ hb]
    rw [show 2*h+2=2*(h+1) by omega, t_double, hu]
    simp)
  have hr2 : X z (2*q)=z+4*q-1 := by
    simpa [show q+1+(q-1)=2*q by omega, show z+2*q+1+2*(q-1)=z+4*q-1 by omega] using hr2raw
  have hrightlast := run_ones_last z (2*q) (z+4*q-1) (2*q) (by omega) hr2 (by
    intro i hi
    have he : z+4*q-1+i+1=(4*h+6)*2^r+i := by
      simp only [Nat.add_mul, Nat.mul_assoc]
      change z+4*q-1+i+1=4*(h*q)+6*q+i
      omega
    rw [he]
    exact block_eq r (4*h+6) 2 2 i (by
      intro j hj
      have hj : j=0 ∨ j=1 := by omega
      rcases hj with rfl | rfl
      · rw [show 4*h+6+0=4*(h+1)+2 by omega]; simp [hu]
      · rw [show 4*h+6+1=4*(h+1)+3 by omega]; simp [hu]) hi)
  apply height_eq_of_boundaries _ (4*q-1) (by change 1≤z-1; omega)
  · have he : z-1+1=z := by omega
    change X (z-1) (4*q-1)<X (z-1+1) (4*q-1)
    rw [he]
    have hl := hleftlast.2
    have hr := hrightlast.2
    have hk : 2*q+2*q-1=4*q-1 := by omega
    rw [hk] at hl hr
    omega
  · have he : z-1+1=z := by omega
    change X (z-1) (4*q-1+1)=X (z-1+1) (4*q-1+1)
    rw [he, show 4*q-1+1=4*q by omega]
    have hl := hleftlast.1
    have hr := hrightlast.1
    have hk : 2*q+2*q=4*q := by omega
    rw [hk] at hl hr
    omega

theorem translate_maximum (d v ell lo hi : Nat) (hv : 1≤v)
    (hm : IsMaximumLength t t v ell) (hlo : lo≤v+1)
    (hhi : X (v+1) (ell+1)<hi)
    (hbits : ∀ w, lo≤w → w<hi → t (d+w)=t w) : height (d+v)=ell := by
  have hm := (maximum_length_iff t t v ell hv).1 hm
  change X v ell<X (v+1) ell ∧ X v (ell+1)=X (v+1) (ell+1) at hm
  have hmono := trajectory_mono t t (show v≤v+1 by omega) (ell+1)
  change X v (ell+1)≤X (v+1) (ell+1) at hmono
  have hl := window_translate d v lo hi (ell+1) hlo (by omega) hbits
  have hr := window_translate d (v+1) lo hi (ell+1) (by omega) hhi hbits
  apply height_eq_of_boundaries _ ell (by omega)
  · rw [show d+v+1=d+(v+1) by omega, hl ell (by omega), hr ell (by omega)]
    omega
  · rw [show d+v+1=d+(v+1) by omega, hl (ell+1) (by omega), hr (ell+1) (by omega), hm.2]

theorem two_block_copy (g r w : Nat) (hg : t g=false) (hu : t (g+1)=true)
    (hw : w<2*2^r) : t (g*2^r+w)=t w := by
  have hb := block_eq r g 0 2 w (by
    intro j hj
    have hj : j=0 ∨ j=1 := by omega
    rcases hj with rfl | rfl <;> simp [hg, hu]) hw
  simpa using hb

theorem special_form (h : Nat) (ha : special h=true) :
    ∃ g, h=4*g+1 ∧ t g=false ∧ t (g+1)=true := by
  have ha' : h%4=1 ∧ t (h/4)=false ∧ t (h/4+1)=true := by
    simpa [special, Bool.and_eq_true, and_assoc] using ha
  exact ⟨h/4, by omega, ha'.2⟩

theorem consecutive_ones (h : Nat) (hh : t h=true) (hu : t (h+1)=true) :
    t (h+2)=false ∧ special h=t (h+3) := by
  have hm := Nat.mod_lt h (by decide : 0<4)
  have hd := Nat.mod_add_div h 4
  have hc : h=4*(h/4) ∨ h=4*(h/4)+1 ∨ h=4*(h/4)+2 ∨ h=4*(h/4)+3 := by omega
  rcases hc with he | he | he | he
  · have hh' : t (h/4)=true := by rw [he, t_four_mul] at hh; exact hh
    have hu' : (!(t (h/4))) = true := by
      rw [he, t_four_mul_one] at hu
      exact hu
    simp [hh'] at hu'
  · have hg : t (h/4)=false := by
      have hh' : (!(t (h/4))) = true := by rw [he, t_four_mul_one] at hh; exact hh
      simpa using hh'
    constructor
    · rw [show h+2=4*(h/4)+3 by omega, t_four_mul_three, hg]
    · have hj : h%4=1 := by omega
      rw [show h+3=4*(h/4+1) by omega, t_four_mul]
      simp [special, hj, hg]
  · have hh' : (!(t (h/4))) = true := by rw [he, t_four_mul_two] at hh; exact hh
    have hu' : t (h/4)=true := by
      rw [show h+1=4*(h/4)+3 by omega, t_four_mul_three] at hu
      exact hu
    simp [hu'] at hh'
  · have hg : t (h/4+1)=true := by
      rw [show h+1=4*(h/4+1) by omega, t_four_mul] at hu
      exact hu
    constructor
    · rw [show h+2=4*(h/4+1)+1 by omega, t_four_mul_one, hg]; rfl
    · rw [show h+3=4*(h/4+1)+2 by omega, t_four_mul_two, hg]
      simp [special, show h%4=3 by omega]

/-- The special odd case is a local translated sharp equality family. -/
theorem odd_special (h r : Nat) (ha : special h=true) :
    height ((4*h+2)*2^r-1)=16*2^r-3 := by
  obtain ⟨g, rfl, hg, hu⟩ := special_form h ha
  let q := 2^r
  let d := g*2^(r+4)
  have hp : 0<q := Nat.two_pow_pos r
  have hpow : 2^(r+1)=2*q := by simp [q, Nat.pow_succ]; omega
  have hpow4 : 2^(r+4)=16*q := by simp [q, Nat.pow_succ]; omega
  have hd : d=16*(g*q) := by dsimp [d]; rw [hpow4]; simp [Nat.mul_left_comm]
  have hst : (4*(4*g+1)+2)*2^r-1=d+(3*2^(r+1)-1) := by
    simp only [Nat.add_mul, Nat.mul_assoc, Nat.one_mul]
    change 4*(4*(g*q)+q)+2*q-1=d+(3*2^(r+1)-1)
    omega
  have hupper := (common_descent (r+1) _ (lower_join (r+1))).2
  have hnext : 3*2^(r+1)-1+1=3*2^(r+1) := by omega
  have htime : 8*2^(r+1)-3+1=8*2^(r+1)-2 := by omega
  rw [hst]
  have ht := translate_maximum d (3*2^(r+1)-1) (8*2^(r+1)-3) 0 (2*2^(r+4))
    (by omega) (sharp_equality_family (r+1)) (by omega) (by
      rw [hnext, htime, hupper]
      omega) (by
      intro w _ hw
      exact two_block_copy g (r+4) w hg hu hw)
  have he : 8*2^(r+1)-3=16*2^r-3 := by rw [hpow]; change 8*(2*q)-3=16*q-3; omega
  simpa only [he] using ht

theorem even_exception (h : Nat) (hh : t h=false) (hu : t (h+1)=true) :
    height ((4*h+2)*2^1-2)=5 := by
  have hb : X 3 6=12 := by decide +kernel
  have ht := translate_maximum (h*2^3) 2 5 0 16 (by decide)
    (sharp_equality_family 0) (by decide) (by change X 3 6<16; omega) (by
      intro w _ hw
      exact two_block_copy h 3 w hh hu hw)
  have hs : (4*h+2)*2^1-2=h*2^3+2 := by omega
  simpa [hs] using ht

theorem canonical_six_join (r : Nat) : X (6*2^r) (6*2^r)=16*2^r-1 := by
  let q := 2^r
  have hp : 0<q := Nat.two_pow_pos r
  have h1raw := run_twos t t (6*q) 0 (6*q) (2*q) rfl (by
    intro i hi
    rw [show 6*q+2*i+1=2*(3*q+i)+1 by omega, t_double_add_one]
    have hb := block_eq r 3 0 2 i (by
      intro j hj
      have hj : j=0 ∨ j=1 := by omega
      rcases hj with rfl | rfl <;> decide +kernel) hi
    have he : t (3*q+i)=t i := by simpa [q] using hb
    rw [he]; simp)
  have h1 : X (6*q) (2*q)=10*q := by simpa [show 6*q+2*(2*q)=10*q by omega] using h1raw
  have h2 : X (6*q) (2*q+1)=10*q+1 := by
    change boundary t (t (2*q)) (X (6*q) (2*q))=10*q+1
    rw [h1]
    simp [boundary, q, t_ten_pow_add_one, t_mul_two_pow]
  have h3raw := run_twos t t (6*q) (2*q+1) (10*q+1) (q-1) h2 (by
    intro i hi
    have hb : 1+i<2^r := by change 1+i<q; omega
    rw [show 10*q+1+2*i+1=2*(5*q+(1+i)) by omega,
      show 2*q+1+i=2*q+(1+i) by omega, t_double,
      t_dyadic_block _ r _ hb, t_dyadic_block _ r _ hb]
    simp)
  have h3 : X (6*q) (3*q)=12*q-1 := by
    simpa [show 2*q+1+(q-1)=3*q by omega, show 10*q+1+2*(q-1)=12*q-1 by omega] using h3raw
  have h4raw := run_ones t t (6*q) (3*q) (12*q-1) (2*q) h3 (by
    intro i hi
    rw [show 12*q-1+i+1=12*q+i by omega]
    exact block_eq r 12 3 2 i (by
      intro j hj
      have hj : j=0 ∨ j=1 := by omega
      rcases hj with rfl | rfl <;> decide +kernel) hi)
  have h4 : X (6*q) (5*q)=14*q-1 := by
    simpa [show 3*q+2*q=5*q by omega, show 12*q-1+2*q=14*q-1 by omega] using h4raw
  have h5 := run_twos t t (6*q) (5*q) (14*q-1) q h4 (by
    intro i hi
    rw [show 14*q-1+2*i+1=2*(7*q+i) by omega, t_double,
      t_dyadic_block _ r _ hi, t_dyadic_block _ r _ hi]
    simp)
  simpa [show 5*q+q=6*q by omega, show 14*q-1+2*q=16*q-1 by omega] using h5

theorem last_three_bits (r : Nat) : t (4*2^r-3)=!(t (4*2^r-1)) := by
  have hp := Nat.two_pow_pos r
  rw [show 4*2^r-3=2*(2*(2^r-1))+1 by omega,
    show 4*2^r-1=2*(2*(2^r-1)+1)+1 by omega,
    t_double_add_one, t_double, t_double_add_one, t_double_add_one]
  simp

/-- The nonspecial odd `11` case: a translated sharp descent followed by `2212…2`. -/
theorem odd_nonspecial (h r : Nat) (hh : t h=true) (hu : t (h+1)=true)
    (ha : special h=false) : height ((4*h+2)*2^r-1)=10*2^r-1 := by
  obtain ⟨hh2, he3⟩ := consecutive_ones h hh hu
  have hh3 : t (h+3)=false := by rw [←he3, ha]
  have hpos : 1≤h := by by_cases hz : h=0; simp [hz] at hh; omega
  let q := 2^r
  let z := (4*h+2)*q
  let d := 4*((h-1)*q)
  let B := (4*h+12)*q
  have hp : 0<q := Nat.two_pow_pos r
  have hz : z=4*(h*q)+2*q := by simp [z, Nat.add_mul, Nat.mul_assoc]
  have hB : B=4*(h*q)+12*q := by simp [B, Nat.add_mul, Nat.mul_assoc]
  have hd : d+4*q=4*(h*q) := by
    have he : (h-1)*q=h*q-q := by rw [Nat.sub_mul]; simp
    have hle := Nat.mul_le_mul_right q hpos
    simp only [Nat.one_mul] at hle
    dsimp [d]
    omega
  have hpow : 2^(r+2)=4*q := by simp [q, Nat.pow_succ]; omega
  have hwindow : ∀ w, 4*q≤w → w<16*q → t (d+w)=t w := by
    intro w hw1 hw2
    let i := w-4*q
    have hi : i<3*2^(r+2) := by dsimp [i]; omega
    have hb := block_eq (r+2) h 1 3 i (by
      intro j hj
      have hj : j=0 ∨ j=1 ∨ j=2 := by omega
      rcases hj with rfl | rfl | rfl <;> simp [hh, hu, hh2]) hi
    have hx : h*2^(r+2)+i=d+w := by rw [hpow]; dsimp [i]; simp only [Nat.mul_left_comm h 4 q]; omega
    have ht : 1*2^(r+2)+i=w := by dsimp [i]; omega
    rwa [hx, ht] at hb
  have hleftRef := upper_coalescence r
  change X (6*q-1) (8*q-2)=2*(8*q-2) at hleftRef
  have hleftCopy := window_translate d (6*q-1) (4*q) (16*q) (8*q-2)
    (by omega) (by rw [hleftRef]; omega) hwindow (8*q-2) (by omega)
  have hrightRef := canonical_six_join r
  change X (6*q) (6*q)=16*q-1 at hrightRef
  have hrightCopy := window_translate d (6*q) (4*q) (16*q) (6*q)
    (by omega) (by rw [hrightRef]; omega) hwindow (6*q) (by omega)
  have hls : d+(6*q-1)=z-1 := by omega
  have hrs : d+6*q=z := by omega
  have hl : X (z-1) (8*q-2)=B-4 := by rw [hls, hleftRef] at hleftCopy; omega
  have hr : X z (6*q)=B-1 := by rw [hrs, hrightRef] at hrightCopy; omega
  have hrightlast := run_ones_last z (6*q) (B-1) (4*q) (by omega) hr (by
    intro i hi
    have he : B-1+i+1=(4*h+12)*2^r+i := by change B-1+i+1=B+i; omega
    rw [he]
    exact block_eq r (4*h+12) 6 4 i (by
      intro j hj
      have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
      rcases hj with rfl | rfl | rfl | rfl
      · rw [show 4*h+12+0=4*(h+3) by omega]; simp [hh3]
      · rw [show 4*h+12+1=4*(h+3)+1 by omega]; simp [hh3]
      · rw [show 4*h+12+2=4*(h+3)+2 by omega]; simp [hh3]
      · rw [show 4*h+12+3=4*(h+3)+3 by omega]; simp [hh3]) hi)
  have hbminus (c : Nat) (hc : c≤4*q) (hcpos : 0<c) : t (B-c)=t (4*q-c) := by
    have he : B-c=(h+2)*2^(r+2)+(4*q-c) := by
      rw [hpow]; simp only [Nat.add_mul, Nat.mul_left_comm h 4 q]
      omega
    rw [he, t_dyadic_block _ _ _ (by omega), hh2]
    simp
  have hl1 : X (z-1) (8*q-1)=B-2 := by
    have hk : 8*q-1=(8*q-2)+1 := by omega
    rw [hk]
    change boundary t (t (8*q-2)) (X (z-1) (8*q-2))=B-2
    rw [hl]
    have hb : t (B-4+1)≠t (8*q-2) := by
      rw [show B-4+1=B-3 by omega, hbminus 3 (by omega) (by omega),
        show 8*q-2=2*(4*q-1) by omega, t_double]
      have he := last_three_bits r
      change t (4*q-3)=!(t (4*q-1)) at he
      rw [he]; simp
    simp [boundary, hb]
    omega
  have hl2 : X (z-1) (8*q)=B := by
    have hk : 8*q=(8*q-1)+1 := by omega
    rw [hk]
    change boundary t (t (8*q-1)) (X (z-1) (8*q-1))=B
    rw [hl1]
    have hb : t (B-2+1)≠t (8*q-1) := by
      rw [show B-2+1=B-1 by omega, hbminus 1 (by omega) (by omega),
        show 8*q-1=2*(4*q-1)+1 by omega, t_double_add_one]
      simp
    simp [boundary, hb]
    omega
  have hl3 : X (z-1) (8*q+1)=B+1 := by
    change boundary t (t (8*q)) (X (z-1) (8*q))=B+1
    rw [hl2]
    have hb : t (B+1)=true := by
      have he : B+1=(2*(2*(h+3)))*2^r+1 := by
        simp only [Nat.add_mul, Nat.mul_assoc]
        change B+1=2*(2*(h*q+3*q))+1
        omega
      rw [he, t_even_mul_pow_one, t_double, hh3]; rfl
    simp [boundary, hb, q, t_mul_two_pow]
  have hleftlast := run_twos_last (z-1) (8*q+1) (B+1) (2*q-1) (by omega) hl3 (by
    intro i hi
    have hb : 1+i<2^(r+1) := by simp only [Nat.pow_succ]; change 1+i<q*2; omega
    have he : B+1+2*i+1=2*((h+3)*2^(r+1)+(1+i)) := by
      simp only [Nat.pow_succ, Nat.add_mul]
      change B+1+2*i+1=2*(h*(q*2)+3*(q*2)+(1+i))
      rw [show h*(q*2)=2*(h*q) by simp [Nat.mul_comm, Nat.mul_left_comm]]
      omega
    have hk : 8*q+1+i=4*2^(r+1)+(1+i) := by simp only [Nat.pow_succ]; change 8*q+1+i=4*(q*2)+(1+i); omega
    rw [he, hk, t_double, t_dyadic_block _ _ _ hb, t_dyadic_block _ _ _ hb, hh3]
    simp)
  apply height_eq_of_boundaries _ (10*q-1) (by change 1≤z-1; omega)
  · change X (z-1) (10*q-1)<X (z-1+1) (10*q-1)
    rw [show z-1+1=z by omega]
    have hl := hleftlast.2
    have hr := hrightlast.2
    rw [show 8*q+1+(2*q-1)-1=10*q-1 by omega] at hl
    rw [show 6*q+4*q-1=10*q-1 by omega] at hr
    omega
  · change X (z-1) (10*q-1+1)=X (z-1+1) (10*q-1+1)
    rw [show z-1+1=z by omega, show 10*q-1+1=10*q by omega]
    have hl := hleftlast.1
    have hr := hrightlast.1
    rw [show 8*q+1+(2*q-1)=10*q by omega] at hl
    rw [show 6*q+4*q=10*q by omega] at hr
    omega

theorem even_seed (h m : Nat) (hh : t h=false)
    (hm : m=0 → t (h+1)=false) :
    X ((4*h+2)*2^(m+1)-2) 5=(4*h+2)*2^(m+1)+5 := by
  let a := (2*h+1)*2^m
  have ha : 1≤a := by
    have hp := Nat.two_pow_pos m
    have ht := Nat.mul_le_mul_right (2^m) (show 1≤2*h+1 by omega)
    simp only [Nat.one_mul] at ht
    simpa [a] using Nat.le_trans hp ht
  have hta : t a=true := by simp [a, t_mul_two_pow, t_double_add_one, hh]
  have htanext : t (a+1)=false := by
    cases m with
    | zero =>
      have hu := hm rfl
      have he : a+1=2*(h+1) := by dsimp [a]; omega
      rw [he, t_double, hu]
    | succ m =>
      have he : a+1=2*((2*h+1)*2^m)+1 := by
        simp [a, Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]
      rw [he, t_double_add_one, t_mul_two_pow, t_double_add_one, hh]
      rfl
  have hz : (4*h+2)*2^(m+1)=4*a := by
    calc
      (4*h+2)*2^(m+1)=((4*h+2)*2)*2^m := by
        simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      _ = 4*a := by
        dsimp [a]
        rw [←Nat.mul_assoc]
        congr 1
        omega
  rw [hz]
  have hb4 : t (4*a+4)=false := by rw [show 4*a+4=4*(a+1) by omega]; simp [htanext]
  have hb5 : t (4*a+5)=true := by rw [show 4*a+5=4*(a+1)+1 by omega]; simp [htanext]
  have he1 : 4*a-2+1=4*a-1 := by omega
  have he2 : 4*a-2+2=4*a := by omega
  have he3 : 4*a-1+1=4*a := by omega
  cases hb : t (4*a-1) <;>
    simp [X, trajectory, boundary, Nat.add_assoc, he1, he2, he3, hb, hta, hb4, hb5]

theorem ascent_high (h d j : Nat) (hh : t h=false) (hd : 2≤d)
    (hsmall : d=2 → t (h+1)=false) (hj : j<4) :
    t ((4*h+2)*2^d+8+j)=t (6+j) := by
  by_cases hd2 : d=2
  · subst d
    have hu := hsmall rfl
    have he : (4*h+2)*2^2+8+j=(h+1)*2^4+j := by omega
    rw [he, t_dyadic_block _ 4 j (by omega), hu]
    have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    rcases hj with rfl | rfl | rfl | rfl <;> decide +kernel
  · by_cases hd3 : d=3
    · subst d
      have he : (4*h+2)*2^3+8+j=(4*h+3)*2^3+j := by omega
      rw [he, t_dyadic_block _ 3 j (by omega), t_four_mul_three, hh]
      have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
      rcases hj with rfl | rfl | rfl | rfl <;> decide +kernel
    · have hp : 16≤2^d := Nat.pow_le_pow_right (n:=2) (by decide) (by omega : 4≤d)
      rw [show (4*h+2)*2^d+8+j=(4*h+2)*2^d+(8+j) by omega,
        t_dyadic_block _ d (8+j) (by omega), t_four_mul_two, hh]
      have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
      rcases hj with rfl | rfl | rfl | rfl <;> decide +kernel

/-- A dyadic ascent block: `s` advances of two followed by `4s` of one. -/
theorem ascent_step (h n d v : Nat) (hh : t h=false) (hd : 2≤d)
    (hsmall : d=2 → t (h+1)=false)
    (hstart : X v (5*2^n)=(4*h+2)*2^(n+d)+6*2^n-1) :
    X v (10*2^n)=(4*h+2)*2^(n+d)+12*2^n-1 := by
  let s := 2^n
  let M := 2^d
  let z := (4*h+2)*2^(n+d)
  have hp : 0<s := Nat.two_pow_pos n
  have hM : 4≤M := Nat.pow_le_pow_right (n:=2) (by decide) hd
  have hz : z=((4*h+2)*M)*s := by
    dsimp [z, M, s]
    rw [Nat.pow_add]
    simp [Nat.mul_comm, Nat.mul_assoc]
  have hhalf : z=2*(((2*h+1)*M)*s) := by
    rw [hz]
    simp only [Nat.add_mul, Nat.mul_assoc, Nat.one_mul]
    omega
  have h1raw := run_twos t t v (5*s) (z+6*s-1) s hstart (by
    intro i hi
    have he : z+6*s-1+2*i+1=2*((((2*h+1)*M)+3)*s+i) := by
      rw [Nat.add_mul]
      omega
    rw [he, t_double, t_dyadic_block _ n i hi, t_dyadic_block _ n i hi]
    have hb : t ((2*h+1)*M+3)=true := by
      rw [t_dyadic_block _ d 3 (by change 3<M; omega), t_double_add_one, hh]
      simp
    rw [hb]
    simp)
  have h1 : X v (6*s)=z+8*s-1 := by
    simpa [show 5*s+s=6*s by omega, show z+6*s-1+2*s=z+8*s-1 by omega] using h1raw
  have h2raw := run_ones t t v (6*s) (z+8*s-1) (4*s) h1 (by
    intro i hi
    have he : z+8*s-1+i+1=(((4*h+2)*M)+8)*s+i := by
      rw [Nat.add_mul]
      omega
    rw [he]
    exact block_eq n (((4*h+2)*M)+8) 6 4 i
      (fun j hj => ascent_high h d j hh hd hsmall hj) hi)
  simpa [show 6*s+4*s=10*s by omega, show z+8*s-1+4*s=z+12*s-1 by omega] using h2raw

/-- The ascent reaches scale `2^m` before crossing the final high-bit boundary. -/
theorem even_rising (h m k : Nat) (hh : t h=false) :
    X ((4*h+2)*2^(m+k+2)-2) (5*2^m)=(4*h+2)*2^(m+k+2)+6*2^m-1 := by
  induction m generalizing k with
  | zero =>
    have he := even_seed h (k+1) hh (by intro hn; omega)
    simpa [show 0+k+2=k+1+1 by omega, show 5*2^0=5 by decide,
      show 6*2^0=6 by decide, show (4*h+2)*2^(k+1+1)+6-1=(4*h+2)*2^(k+1+1)+5 by omega] using he
  | succ m ih =>
    have hi := ih (k+1)
    have hs : m+(k+1)+2=m+(k+3) := by omega
    rw [hs] at hi
    have he := ascent_step h m (k+3) ((4*h+2)*2^(m+(k+3))-2) hh (by omega) (by intro hn; omega) hi
    have hs2 : m+1+k+2=m+(k+3) := by omega
    rw [hs2]
    have hp : 2^(m+1)=2*2^m := by rw [Nat.pow_succ]; omega
    simpa [hp, show 5*(2*2^m)=10*2^m by omega,
      show 6*(2*2^m)=12*2^m by omega] using he

theorem even_rising_zero (h m : Nat) (hh : t h=false) (hu : t (h+1)=false) :
    X ((4*h+2)*2^(m+1)-2) (5*2^m)=(4*h+2)*2^(m+1)+6*2^m-1 := by
  cases m with
  | zero =>
    have he := even_seed h 0 hh (fun _ => hu)
    simpa [show (4*h+2)*2^1+6-1=(4*h+2)*2^1+5 by omega] using he
  | succ m =>
    have hi := even_rising h m 0 hh
    simp only [Nat.add_zero] at hi
    have he := ascent_step h m 2 ((4*h+2)*2^(m+2)-2) hh (by decide) (fun _ => hu) hi
    have hp : 2^(m+1)=2*2^m := by rw [Nat.pow_succ]; omega
    simpa [show m+1+1=m+2 by omega, hp, show 5*(2*2^m)=10*2^m by omega,
      show 6*(2*2^m)=12*2^m by omega] using he

/-- The common final configuration for both long even branches. -/
theorem even_finish (a n : Nat) (ha : 2≤a)
    (hstart : X (2*a*2^n-2) (5*2^n)=2*a*2^n+6*2^n-1)
    (hleft : ∀ j, j<3 → t (a+3+j)≠t (5+j))
    (hright : ∀ j, j<4 → t (a+j)≠t j)
    (hlast : ∀ j, j<4 → t (2*a+8+j)=t (4+j)) :
    height (2*a*2^n-2)=8*2^n-1 := by
  let s := 2^n
  let z := 2*a*s
  have hp : 0<s := Nat.two_pow_pos n
  have hz : z=2*(a*s) := by simp [z, Nat.mul_assoc]
  have hzp : 4≤z := by
    have hl := Nat.mul_le_mul_right s ha
    omega
  have hl := run_twos_last (z-2) (5*s) (z+6*s-1) (3*s) (by omega) hstart (by
    intro i hi
    rw [show z+6*s-1+2*i+1=2*((a+3)*s+i) by rw [Nat.add_mul]; omega,
      t_double]
    exact block_ne n (a+3) 5 3 i hleft hi)
  have hr1raw := run_twos t t (z-1) 0 (z-1) (4*s) rfl (by
    intro i hi
    rw [show z-1+2*i+1=2*(a*s+i) by omega, t_double]
    have he := block_ne n a 0 4 i (by simpa using hright) hi
    simpa using he)
  have hr1 : X (z-1) (4*s)=z+8*s-1 := by
    simpa [show z-1+2*(4*s)=z+8*s-1 by omega] using hr1raw
  have hr := run_ones_last (z-1) (4*s) (z+8*s-1) (4*s) (by omega) hr1 (by
    intro i hi
    rw [show z+8*s-1+i+1=(2*a+8)*s+i by rw [Nat.add_mul]; omega]
    exact block_eq n (2*a+8) 4 4 i hlast hi)
  apply height_eq_of_boundaries _ (8*s-1) (by change 1≤z-2; omega)
  · change X (z-2) (8*s-1)<X (z-2+1) (8*s-1)
    rw [show z-2+1=z-1 by omega]
    have hl := hl.2
    have hr := hr.2
    rw [show 5*s+3*s-1=8*s-1 by omega] at hl
    rw [show 4*s+4*s-1=8*s-1 by omega] at hr
    omega
  · change X (z-2) (8*s-1+1)=X (z-2+1) (8*s-1+1)
    rw [show z-2+1=z-1 by omega, show 8*s-1+1=8*s by omega]
    have hl := hl.1
    have hr := hr.1
    rw [show 5*s+3*s=8*s by omega] at hl
    rw [show 4*s+4*s=8*s by omega] at hr
    omega

theorem even_false_false (h m : Nat) (hh : t h=false) (hu : t (h+1)=false) :
    height ((4*h+2)*2^(m+1)-2)=4*2^(m+1)-1 := by
  have hi := even_rising_zero h m hh hu
  have hp : (4*h+2)*2^(m+1)=2*(4*h+2)*2^m := by
    simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  rw [hp] at hi ⊢
  have he := even_finish (4*h+2) m (by omega) hi (by
    intro j hj
    have hj : j=0 ∨ j=1 ∨ j=2 := by omega
    rcases hj with rfl | rfl | rfl
    · rw [show 4*h+2+3+0=4*(h+1)+1 by omega]; simp [hu]
    · rw [show 4*h+2+3+1=4*(h+1)+2 by omega]; simp [hu]
    · rw [show 4*h+2+3+2=4*(h+1)+3 by omega]; simp [hu]) (by
    intro j hj
    have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    rcases hj with rfl | rfl | rfl | rfl
    · simp [hh]
    · simp [hh]
    · rw [show 4*h+2+2=4*(h+1) by omega]; simp [hu]
    · rw [show 4*h+2+3=4*(h+1)+1 by omega]; simp [hu]) (by
    intro j hj
    rw [show 2*(4*h+2)+8+j=(2*(h+1)+1)*2^2+j by omega,
      show 4+j=1*2^2+j by omega,
      t_dyadic_block _ 2 j hj, t_dyadic_block _ 2 j hj,
      t_double_add_one, hu]
    simp)
  have ht : 4*2^(m+1)-1=8*2^m-1 := by rw [Nat.pow_succ]; omega
  simpa [ht] using he

theorem even_false_true (h m : Nat) (hh : t h=false) (hu : t (h+1)=true) :
    height ((4*h+2)*2^(m+2)-2)=2*2^(m+2)-1 := by
  have hi := even_rising h m 0 hh
  simp only [Nat.add_zero] at hi
  have hp : (4*h+2)*2^(m+2)=2*(8*h+4)*2^m := by
    have hp : 2^(m+2)=4*2^m := by simp [Nat.pow_succ]; omega
    rw [hp, ←Nat.mul_assoc]
    congr 1
    omega
  rw [hp] at hi ⊢
  have he := even_finish (8*h+4) m (by omega) hi (by
    intro j hj
    have hj : j=0 ∨ j=1 ∨ j=2 := by omega
    rcases hj with rfl | rfl | rfl
    · rw [show 8*h+4+3+0=2*(4*h+3)+1 by omega, t_double_add_one]; simp [hh]
    · rw [show 8*h+4+3+1=(h+1)*2^3 by omega, t_mul_two_pow]; simp [hu]
    · rw [show 8*h+4+3+2=2*(4*(h+1))+1 by omega, t_double_add_one]; simp [hu]) (by
    intro j hj
    rw [show 8*h+4+j=(2*h+1)*2^2+j by omega,
      t_dyadic_block _ 2 j hj, t_double_add_one, hh]
    simp) (by
    intro j hj
    rw [show 2*(8*h+4)+8+j=(h+1)*2^4+j by omega,
      show 4+j=1*2^2+j by omega,
      t_dyadic_block _ 4 j (by omega), t_dyadic_block _ 2 j hj, hu]
    simp)
  have ht : 2*2^(m+2)-1=8*2^m-1 := by simp only [Nat.pow_succ]; omega
  simpa [ht] using he

theorem even_formula (h r : Nat) : height ((4*h+2)*2^r-2)=evenValue h r := by
  cases hh : t h with
  | true => simpa [evenValue, hh] using even_true h r hh
  | false =>
    cases r with
    | zero =>
      have hs : (4*h+2)*2^0-2=4*h := by omega
      rw [hs]
      have he := even_scale_one h hh
      cases hu : t (h+1) <;> simpa [evenValue, hh, hu, bit] using he
    | succ r =>
      cases hu : t (h+1) with
      | false =>
        have he := even_false_false h r hh hu
        by_cases hr : r=0
        · subst r; simpa [evenValue, hh, hu, bit] using he
        · simpa [evenValue, hh, hu, bit, hr] using he
      | true =>
        cases r with
        | zero => simpa [evenValue, hh, hu, bit] using even_exception h hh hu
        | succ r =>
          have he := even_false_true h r hh hu
          simpa [evenValue, hh, hu, bit, show r+1+1≠1 by omega, show r+1+1=r+2 by omega] using he

theorem odd_formula (h r : Nat) : height ((4*h+2)*2^r-1)=oddValue h r := by
  cases hh : t h with
  | false => simpa [oddValue, hh] using odd_false h r hh
  | true =>
    cases hu : t (h+1) with
    | false => simpa [oddValue, hh, hu] using odd_true_false h r hh hu
    | true =>
      cases ha : special h with
      | false => simpa [oddValue, hh, hu, ha] using odd_nonspecial h r hh hu ha
      | true => simpa [oddValue, hh, hu, ha] using odd_special h r ha

/-- The full closed form gives the actual attained graph maximum at every start. -/
theorem height_formula : FormulaSpec height :=
  ⟨height_zero, fun h r => ⟨even_formula h r, odd_formula h r⟩⟩

theorem maximum_iff_height (v ell : Nat) : IsMaximumPrefix t v ell ↔ ell=height v := by
  constructor
  · intro hm; exact (height_eq_of_maximum v ell hm).symm
  · intro he; rw [he]; exact height_isMaximum v

private theorem positive_factorization (x : Nat) (hx : 0<x) :
    ∃ h r, x=(2*h+1)*2^r := by
  induction x using Nat.strongRecOn with
  | ind x ih =>
    by_cases ho : x%2=1
    · exact ⟨x/2, 0, by simp; omega⟩
    · obtain ⟨h, r, he⟩ := ih (x/2) (by omega) (by omega)
      refine ⟨h, r+1, ?_⟩
      calc
        x=2*(x/2) := by omega
        _=(2*h+1)*2^(r+1) := by
          rw [he, Nat.pow_succ]
          simp [Nat.mul_comm, Nat.mul_left_comm]

/-- Evaluate the actual maximum from any valid odd-times-power factorization. -/
theorem height_from_factorization (v h r : Nat)
    (hf : v/2+1=(2*h+1)*2^r) :
    height v = if v%2=0 then evenValue h r else oddValue h r := by
  have hz : (4*h+2)*2^r=2*(v/2+1) := by
    calc
      (4*h+2)*2^r=(2*(2*h+1))*2^r := by congr 1; omega
      _=2*(v/2+1) := by rw [Nat.mul_assoc, ←hf]
  by_cases hv : v%2=0
  · rw [if_pos hv]
    have he : (4*h+2)*2^r-2=v := by omega
    simpa only [he] using even_formula h r
  · rw [if_neg hv]
    have he : (4*h+2)*2^r-1=v := by omega
    simpa only [he] using odd_formula h r

/-- Every natural starting vertex is covered by the formula, including zero. -/
theorem height_closed_form (v : Nat) :
    ∃ h r, v/2+1=(2*h+1)*2^r ∧
      height v = if v%2=0 then evenValue h r else oddValue h r := by
  obtain ⟨h, r, hf⟩ := positive_factorization (v/2+1) (by omega)
  exact ⟨h, r, hf, height_from_factorization v h r hf⟩

#print axioms height_isMaximum
#print axioms even_rising
#print axioms odd_nonspecial
#print axioms height_formula
#print axioms height_from_factorization
#print axioms height_closed_form

end FullHeight
