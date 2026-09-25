import SamuelAlexanderResearch.PhaseHeight
import SamuelAlexanderResearch.PhaseExtremal

/-!
Exact decomposition of finite edits into their finite reachable frontier and
the actual shifted Thue--Morse maximum. Every start, including zero and starts
whose matching prefixes die before the edit cutoff, is covered.
-/

namespace FiniteEditExact

open BinaryAvoidance QuantitativeAvoidance FiniteEditStability PhaseShift PhaseHeight

theorem shifts_eq_of_agree (s other : Nat → Bool) (m : Nat)
    (hag : AgreeFrom s other m) : shift s m = shift other m := by
  funext k
  exact hag (k+m) (by omega)

theorem frontier_bounds (s : Nat → Bool) (v m w : Nat) (hw : w ∈ frontier s v m) :
    2*m ≤ w ∧ v+m ≤ w ∧ w ≤ v+2*m := by
  obtain ⟨path, hv, hend, hm⟩ := (mem_frontier s v m w).mp hw
  have hlo := prefix_lower_bound s path m hm m (Nat.le_refl _)
  have hd := prefix_displacement s path m hm m (Nat.le_refl _)
  omega

/-- Exact concatenation at the edit cutoff. The finite own-target lower
bound makes subtraction by `2*m` legal at every suffix vertex. -/
theorem prefix_decomposition (s other : Nat → Bool) (m : Nat)
    (hag : AgreeFrom s other m) (v len : Nat) :
    HasPrefix s v (m+len) ↔ ∃ w, w ∈ frontier s v m ∧
      HasPrefix (shift other m) (w-2*m) len := by
  have hshift := shifts_eq_of_agree s other m hag
  constructor
  · rintro ⟨path, hv, hm⟩
    refine ⟨path m, (mem_frontier s v m (path m)).mpr
      ⟨path, hv, rfl, fun k hk => hm k (by omega)⟩, ?_⟩
    have htail := suffix_subtraction s path (m+len) m hm (by omega)
    have hlen : m+len-m = len := by omega
    rw [hlen, hshift] at htail
    exact ⟨subtractSuffix path m, by simp [subtractSuffix], htail⟩
  · rintro ⟨w, hw, tailPath, hstart, hmatch⟩
    obtain ⟨front, hv, hend, hfront⟩ := (mem_frontier s v m w).mp hw
    have hlow := (frontier_bounds s v m w hw).1
    have htail : MatchesPrefix (shift s m) tailPath len := by
      simpa only [hshift] using hmatch
    let tail := fun k => tailPath (k-m) + 2*m
    have hjoin : front m = tail m := by
      simp only [tail, Nat.sub_self, hstart]
      omega
    have hedges : ∀ k, m ≤ k → k < m+len → Edge s (tail k) (tail (k+1)) (s k) := by
      intro k hmk hk
      have he := prefix_translate s m tailPath len htail (k-m) (by omega)
      have hnext : k+1-m = (k-m)+1 := by omega
      have hphase : k-m+m = k := by omega
      simpa only [tail, hnext, hphase] using he
    obtain ⟨path, hzero, hpath, _⟩ := splice_prefix s front tail m (m+len) hfront hjoin hedges
    exact ⟨path, hzero.trans hv, hpath⟩

/-- The suffix predicate is replaced by the proved actual shifted height. -/
theorem thue_prefix_decomposition (s : Nat → Bool) (m : Nat)
    (hag : AgreeFrom s ThueMorseBits.t m) (v len : Nat) :
    HasPrefix s v (m+len) ↔ ∃ w, w ∈ frontier s v m ∧
      len ≤ PhaseHeight.height m (w-2*m) := by
  rw [prefix_decomposition s ThueMorseBits.t m hag]
  simp only [PhaseHeight.hasPrefix_iff_le_height]

def maxSuffix (m : Nat) : List Nat → Nat
  | [] => 0
  | w :: rest => max (PhaseHeight.height m (w-2*m)) (maxSuffix m rest)

theorem le_maxSuffix (m : Nat) (xs : List Nat) (w : Nat) (hw : w ∈ xs) :
    PhaseHeight.height m (w-2*m) ≤ maxSuffix m xs := by
  induction xs with
  | nil => simp at hw
  | cons x rest ih =>
    rcases List.mem_cons.mp hw with he | hrest
    · subst w
      exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hrest) (Nat.le_max_right _ _)

theorem maxSuffix_attained (m : Nat) (xs : List Nat) (hne : xs ≠ []) :
    ∃ w, w ∈ xs ∧ maxSuffix m xs = PhaseHeight.height m (w-2*m) := by
  induction xs with
  | nil => exact False.elim (hne rfl)
  | cons x rest ih =>
    by_cases hrest : rest = []
    · subst rest
      exact ⟨x, by simp, by simp [maxSuffix]⟩
    · obtain ⟨w, hw, he⟩ := ih hrest
      by_cases hle : PhaseHeight.height m (x-2*m) ≤ maxSuffix m rest
      · refine ⟨w, by simp [hw], ?_⟩
        change max (PhaseHeight.height m (x-2*m)) (maxSuffix m rest) = _
        rw [Nat.max_eq_right hle, he]
      · refine ⟨x, by simp, ?_⟩
        exact Nat.max_eq_left (by omega)

/-- A finite exact algorithm: early extinction is checked before `m`; a
nonempty cutoff frontier uses the maximum of its actual shifted heights. -/
def height (s : Nat → Bool) (m v : Nat) : Nat :=
  if frontier s v m = [] then boundedHeight s v m else m + maxSuffix m (frontier s v m)

theorem height_isMaximum (s : Nat → Bool) (m : Nat)
    (hag : AgreeFrom s ThueMorseBits.t m) (v : Nat) :
    IsMaximumPrefix s v (height s m v) := by
  by_cases hempty : frontier s v m = []
  · simp only [height, if_pos hempty]
    apply boundedHeight_isMaximum
    intro len hlen
    by_cases hsmall : len ≤ m
    · exact hsmall
    · have hprefix := hasPrefix_mono s v m len (by omega) hlen
      exact False.elim ((hasPrefix_iff_frontier_nonempty s v m).mp hprefix hempty)
  · simp only [height, if_neg hempty]
    obtain ⟨w, hw, hmax⟩ := maxSuffix_attained m (frontier s v m) hempty
    refine ⟨(thue_prefix_decomposition s m hag v _).mpr ⟨w, hw, by omega⟩, ?_⟩
    intro len hlen
    by_cases hsmall : len < m
    · omega
    · have he : len = m+(len-m) := by omega
      have hlong : HasPrefix s v (m+(len-m)) := by simpa only [← he] using hlen
      obtain ⟨z, hz, htail⟩ := (thue_prefix_decomposition s m hag v (len-m)).mp hlong
      have hb := le_maxSuffix m (frontier s v m) z hz
      omega

/-- No supplied finite bound, positive-start restriction, or choice of a
successful continuation occurs in this exact maximum formula. -/
theorem maximum_iff_height (s : Nat → Bool) (m : Nat)
    (hag : AgreeFrom s ThueMorseBits.t m) (v len : Nat) :
    IsMaximumPrefix s v len ↔ len = height s m v := by
  constructor
  · intro hm
    have hh := height_isMaximum s m hag v
    exact Nat.le_antisymm (hh.2 len hm.1) (hm.2 _ hh.1)
  · intro he
    subst len
    exact height_isMaximum s m hag v

theorem hasPrefix_iff_le_height (s : Nat → Bool) (m : Nat)
    (hag : AgreeFrom s ThueMorseBits.t m) (v len : Nat) :
    HasPrefix s v len ↔ len ≤ height s m v :=
  hasPrefix_iff_le_maximum s v _ len (height_isMaximum s m hag v)

theorem nonempty_height_formula (s : Nat → Bool) (m v : Nat)
    (hne : frontier s v m ≠ []) :
    height s m v = m + maxSuffix m (frontier s v m) := by
  simp only [height, if_neg hne]

theorem early_extinction (s : Nat → Bool) (m : Nat)
    (hag : AgreeFrom s ThueMorseBits.t m) (v : Nat) (hempty : frontier s v m = []) :
    height s m v < m := by
  have hm := height_isMaximum s m hag v
  by_cases h : height s m v < m
  · exact h
  · have hprefix := hasPrefix_mono s v m (height s m v) (by omega) hm.1
    exact False.elim ((hasPrefix_iff_frontier_nonempty s v m).mp hprefix hempty)

theorem prefix_upper_between (s : Nat → Bool) (path : Nat → Nat) (len : Nat)
    (hm : MatchesPrefix s path len) (i j : Nat) (hij : i ≤ j) (hj : j ≤ len) :
    path j ≤ path i + 2*(j-i) := by
  induction j with
  | zero =>
    have hi : i = 0 := by omega
    simp [hi]
  | succ j ih =>
    by_cases hi : i ≤ j
    · have hb := ih hi (by omega)
      have he := edge_displacement s (path j) (path (j+1)) (s j) (hm j (by omega))
      omega
    · have hi' : i = j+1 := by omega
      simp [hi']

/-- Saturation of the universal finite-edit allowance forces maximum forward
displacement throughout the edited prefix. -/
theorem equality_prefix_twos (s : Nat → Bool) (m : Nat)
    (hag : AgreeFrom s ThueMorseBits.t m) (path : Nat → Nat) (len : Nat)
    (hv : 1 ≤ path 0) (hm : MatchesPrefix s path len)
    (heq : 3*len = 8*path 0+8*m-1) :
    m ≤ len ∧ ∀ k, k ≤ m → path k = path 0+2*k := by
  have hml : m ≤ len := by omega
  obtain ⟨changed, hc, hle, _, hsuffix⟩ :=
    finite_edit_transport s ThueMorseBits.t m hag path len hm
  have hpos : 1 ≤ changed 0 := by
    by_cases hz : changed 0 = 0
    · have h := thue_zero_prefix_bound changed len hz hc
      omega
    · omega
  have hb := SharpThueMorse.binary_path_prefix_bound changed len hpos hc
  have hstart : changed 0 = path 0+m := by omega
  have hs := hsuffix m (Nat.min_le_left _ _)
  have hd := prefix_displacement s path len hm m hml
  have hcd := prefix_displacement ThueMorseBits.t changed len hc m hml
  have hend : path m = path 0+2*m := by omega
  refine ⟨hml, ?_⟩
  intro k hk
  have hupper := prefix_displacement s path len hm k (by omega)
  have hbetween := prefix_upper_between s path len hm k m hk hml
  omega

/-- An explicit finite bit test: the first m edges all advance by two. -/
def TwoPrefix (s : Nat → Bool) (v m : Nat) : Prop :=
  ∀ k, k < m → s k = !(row s (v+2*k+2))

theorem twoPrefix_matches (s : Nat → Bool) (v m : Nat) (h : TwoPrefix s v m) :
    MatchesPrefix s (fun k => v+2*k) m := by
  intro k hk
  change Edge s (v+2*k) (v+2*(k+1)) (s k)
  refine ⟨by omega, Or.inr ⟨by omega, ?_⟩⟩
  have he : v+2*(k+1) = v+2*k+2 := by omega
  simpa only [he] using h k hk

/-- Equality locations for an individual finite edit are exactly the dyadic
locations which pass the displayed finite bit test. -/
theorem finite_edit_extremal_iff (s : Nat → Bool) (m : Nat)
    (hag : AgreeFrom s ThueMorseBits.t m) (v len : Nat) (hv : 1 ≤ v) :
    (IsMaximumPrefix s v len ∧ 3*len = 8*v+8*m-1) ↔
      ∃ n, m ≤ 2^n ∧ v = 3*2^n-m-1 ∧ len = 8*2^n-3 ∧ TwoPrefix s v m := by
  constructor
  · rintro ⟨hmax, heq⟩
    obtain ⟨path, hzero, hm⟩ := hmax.1
    obtain ⟨hml, htwos⟩ := equality_prefix_twos s m hag path len
      (by omega) hm (by simpa only [hzero] using heq)
    have hcut := suffix_subtraction s path len m hm hml
    rw [shifts_eq_of_agree s ThueMorseBits.t m hag] at hcut
    have hstart : subtractSuffix path m 0 = v := by
      simp only [subtractSuffix, Nat.zero_add, htwos m (Nat.le_refl _), hzero]
      omega
    have hshiftEq : 3*(len-m) = 8*(subtractSuffix path m 0)+5*m-1 := by omega
    obtain ⟨n, hn, hloc, hlen⟩ := PhaseExtremal.shifted_equality_necessary m
      (subtractSuffix path m) (len-m) (by omega) hcut hshiftEq
    have hp := Nat.two_pow_pos n
    refine ⟨n, hn, by omega, by omega, ?_⟩
    intro k hk
    have he := hm k (by omega)
    rw [htwos k (by omega), htwos (k+1) (by omega), hzero] at he
    rcases he.2 with hone | htwo
    · omega
    · have hindex : v+2*(k+1) = v+2*k+2 := by omega
      simpa only [hindex] using htwo.2
  · rintro ⟨n, hn, hloc, hlen, htwos⟩
    have hp := Nat.two_pow_pos n
    have hfront : v+2*m ∈ frontier s v m := by
      apply (mem_frontier s v m (v+2*m)).mpr
      exact ⟨fun k => v+2*k, by simp, rfl, twoPrefix_matches s v m htwos⟩
    have htail : HasPrefix (shift ThueMorseBits.t m) ((v+2*m)-2*m) (8*2^n-m-3) := by
      have hx : (v+2*m)-2*m = 3*2^n-m-1 := by omega
      rw [hx]
      exact PhaseExtremal.shifted_family_prefix n m hn
    have hlong := (prefix_decomposition s ThueMorseBits.t m hag v (8*2^n-m-3)).mpr
      ⟨v+2*m, hfront, htail⟩
    have hlength : m+(8*2^n-m-3) = len := by omega
    have heq : 3*len = 8*v+8*m-1 := by omega
    refine ⟨⟨by simpa only [hlength] using hlong, ?_⟩, heq⟩
    intro ell ⟨path, hz, hm⟩
    have hb := finite_edit_thue_upper s m hag path ell (by omega) hm
    omega

/-- A finite edit chosen to make the critical prefix use only two-steps. -/
def sharpEdit (m n : Nat) (k : Nat) : Bool :=
  if k < m then !(ThueMorseBits.t (3*2^n-m-1+2*k+2)) else ThueMorseBits.t k

theorem sharpEdit_agree (m n : Nat) : AgreeFrom (sharpEdit m n) ThueMorseBits.t m := by
  intro k hk
  simp [sharpEdit, show ¬k<m by omega]

theorem sharpEdit_twoPrefix (m n : Nat) (hn : m+1 ≤ 2^n) :
    TwoPrefix (sharpEdit m n) (3*2^n-m-1) m := by
  intro k hk
  have hw : 2*m ≤ 3*2^n-m-1+2*k+2 := by omega
  have hr := row_eq_of_agree (sharpEdit m n) ThueMorseBits.t m (sharpEdit_agree m n)
    (3*2^n-m-1+2*k+2) hw
  rw [hr, SharpThueMorse.binary_row_eq]
  simp only [sharpEdit, if_pos hk]

/-- For every edit cutoff, the universal additive constant is attained by an
actual finitely edited population at the displayed positive start. -/
theorem sharpEdit_equality (m n : Nat) (hn : m+1 ≤ 2^n) :
    IsMaximumPrefix (sharpEdit m n) (3*2^n-m-1) (8*2^n-3) ∧
      3*(8*2^n-3) = 8*(3*2^n-m-1)+8*m-1 := by
  apply (finite_edit_extremal_iff (sharpEdit m n) m (sharpEdit_agree m n)
    (3*2^n-m-1) (8*2^n-3) (by omega)).mpr
  exact ⟨n, by omega, rfl, rfl, sharpEdit_twoPrefix m n hn⟩

def UniversalAdditiveBound (m : Nat) (B : Int) : Prop :=
  ∀ s, AgreeFrom s ThueMorseBits.t m → ∀ v len, 1 ≤ v →
    IsMaximumPrefix s v len → 3*(len : Int) ≤ 8*(v : Int)+B

/-- The best universal integer allowance for edits below m is exactly 8m-1.
The Int formulation includes the unedited value -1 at m=0. -/
theorem optimal_universal_additive_constant (m : Nat) (B : Int) :
    UniversalAdditiveBound m B ↔ 8*(m : Int)-1 ≤ B := by
  constructor
  · intro hb
    let n := m+1
    have hn : m+1 ≤ 2^n := by
      have h := ThueMorseBits.index_lt_two_pow n
      dsimp [n] at *
      omega
    obtain ⟨hmax, heq⟩ := sharpEdit_equality m n hn
    have hv : 1 ≤ 3*2^n-m-1 := by omega
    have h := hb (sharpEdit m n) (sharpEdit_agree m n) _ _ hv hmax
    omega
  · intro hb s hag v len hv hmax
    obtain ⟨path, hz, hm⟩ := hmax.1
    have h := finite_edit_thue_upper s m hag path len (by omega) hm
    omega

end FiniteEditExact

#print axioms FiniteEditExact.prefix_decomposition
#print axioms FiniteEditExact.thue_prefix_decomposition
#print axioms FiniteEditExact.height_isMaximum
#print axioms FiniteEditExact.maximum_iff_height
#print axioms FiniteEditExact.early_extinction
#print axioms FiniteEditExact.finite_edit_extremal_iff
#print axioms FiniteEditExact.sharpEdit_equality
#print axioms FiniteEditExact.optimal_universal_additive_constant
