import SamuelAlexanderResearch.QuantitativeAvoidance
import SamuelAlexanderResearch.SharpThueMorse
import SamuelAlexanderResearch.BinaryPopulation

/-!
Finite changes to a target preserve every finite matching length in its actual
target-dependent graph, with a controlled change of starting vertex.
-/

namespace FiniteEditStability
open BinaryAvoidance QuantitativeAvoidance

/-- Every actual edge advances by one or two vertices. -/
theorem edge_displacement (s : Nat → Bool) (u v : Nat) (b : Bool)
    (he : Edge s u v b) : u+1 ≤ v ∧ v ≤ u+2 := by
  rcases he.2 with he | he <;> omega

/-- The own-target offset invariant holds at every stage of a finite match. -/
theorem prefix_lower_bound (s : Nat → Bool) (path : Nat → Nat) (ell : Nat)
    (hpath : MatchesPrefix s path ell) (k : Nat) (hk : k ≤ ell) : 2*k ≤ path k := by
  induction k with
  | zero => omega
  | succ k ih =>
    have hl := ih (by omega)
    obtain ⟨_, ⟨step, label⟩ | ⟨step, _⟩⟩ := hpath k (by omega)
    · by_cases he : path k = 2*k
      · have hw : path (k+1) = 2*k+1 := by omega
        rw [hw, row_odd] at label
        cases hs : s k <;> simp [hs] at label
      · omega
    · omega

/-- A length-k prefix advances between k and 2k positions. -/
theorem prefix_displacement (s : Nat → Bool) (path : Nat → Nat) (ell : Nat)
    (hpath : MatchesPrefix s path ell) (k : Nat) (hk : k ≤ ell) :
    path 0+k ≤ path k ∧ path k ≤ path 0+2*k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hl := ih (by omega)
    have he := edge_displacement s (path k) (path (k+1)) (s k) (hpath k (by omega))
    omega

/-- Any target prefix can be built backward from a destination at least 2r.
All backward destinations are therefore genuine nonroots with both parents. -/
theorem backward_prefix (s : Nat → Bool) (r w : Nat) (hw : 2*r ≤ w) :
    ∃ path : Nat → Nat, path r = w ∧ MatchesPrefix s path r ∧
      path 0+r ≤ w ∧ w ≤ path 0+2*r := by
  induction r generalizing w with
  | zero =>
    exact ⟨fun _ => w, rfl, fun k hk => by omega, by simp, by simp⟩
  | succ r ih =>
    obtain ⟨u, he⟩ := BinaryPopulation.incoming_each_label s w (by omega) (s r)
    have hd := edge_displacement s u w (s r) he
    obtain ⟨front, hp, hm, hlow, hupp⟩ := ih u (by omega)
    let path := fun k => if k ≤ r then front k else w
    have hzero : path 0 = front 0 := by simp [path]
    refine ⟨path, by simp [path, show ¬r+1 ≤ r by omega], ?_, ?_, ?_⟩
    · intro k hk
      by_cases hkr : k < r
      · simpa [path, show k ≤ r by omega, show k+1 ≤ r by omega] using hm k hkr
      · have hke : k = r := by omega
        subst k
        simpa [path, hp, show ¬r+1 ≤ r by omega] using he
    · rw [hzero]
      omega
    · rw [hzero]
      omega

/-- Splice an actual matching prefix to a correctly phased suffix at the same vertex. -/
theorem splice_prefix (s : Nat → Bool) (front tail : Nat → Nat) (r ell : Nat)
    (hprefix : MatchesPrefix s front r) (hjoin : front r = tail r)
    (htail : ∀ k, r ≤ k → k < ell → Edge s (tail k) (tail (k+1)) (s k)) :
    ∃ path : Nat → Nat, path 0 = front 0 ∧ MatchesPrefix s path ell ∧
      ∀ k, r ≤ k → path k = tail k := by
  let path := fun k => if k ≤ r then front k else tail k
  have hlate : ∀ k, r ≤ k → path k = tail k := by
    intro k hk
    by_cases he : k = r
    · subst k
      simpa [path] using hjoin
    · simp [path, show ¬k ≤ r by omega]
  refine ⟨path, by simp [path], ?_, hlate⟩
  intro k hk
  by_cases he : k < r
  · simpa [path, show k ≤ r by omega, show k+1 ≤ r by omega] using hprefix k he
  · rw [hlate k (by omega), hlate (k+1) (by omega)]
    exact htail k (by omega) hk

/-- Extract an actual finite path from the interval model's Thue-Morse reachability. -/
theorem reachable_thue_prefix (v ell w : Nat)
    (hr : SamuelAlexanderResearch.ThueMorseBound.Reachable
      ThueMorseBits.t ThueMorseBits.t v ell w) :
    ∃ path : Nat → Nat, path 0 = v ∧ path ell = w ∧
      MatchesPrefix ThueMorseBits.t path ell := by
  induction ell generalizing w with
  | zero =>
    change w = v at hr
    subst w
    exact ⟨fun _ => v, rfl, rfl, fun k hk => by omega⟩
  | succ ell ih =>
    obtain ⟨u, hreach, he⟩ := hr
    obtain ⟨front, hzero, hend, hm⟩ := ih u hreach
    let path := fun k => if k ≤ ell then front k else w
    refine ⟨path, by simpa [path] using hzero,
      by simp [path, show ¬ell+1 ≤ ell by omega], ?_⟩
    intro k hk
    by_cases hsmall : k < ell
    · simpa [path, show k ≤ ell by omega, show k+1 ≤ ell by omega] using hm k hsmall
    · have hke : k = ell := by omega
      subst k
      have hb := (SharpThueMorse.binary_edge_iff u w (ThueMorseBits.t ell)).2 he
      simpa [path, hend, show ¬ell+1 ≤ ell by omega] using hb

/-- The checked sharp dyadic family supplies actual path functions in P_t. -/
theorem sharp_family_prefix (n : Nat) :
    ∃ path : Nat → Nat, path 0 = 3*2^n-1 ∧
      MatchesPrefix ThueMorseBits.t path (8*2^n-3) := by
  obtain ⟨w, hw⟩ := (SharpThueMorse.sharp_equality_family n).1
  obtain ⟨path, hzero, _, hm⟩ := reachable_thue_prefix _ _ w hw
  exact ⟨path, hzero, hm⟩

/-- Only the positions below m may differ. -/
def AgreeFrom (s t : Nat → Bool) (m : Nat) : Prop :=
  ∀ k, m ≤ k → s k = t k

theorem row_eq_of_agree (s t : Nat → Bool) (m : Nat) (hag : AgreeFrom s t m)
    (w : Nat) (hw : 2*m ≤ w) : row s w = row t w := by
  have he := hag (w/2) (by omega)
  simp only [row, he]

/-- Beyond both edit thresholds the actual edge and target label are unchanged. -/
theorem tail_edge_transfer (s t : Nat → Bool) (m : Nat) (hag : AgreeFrom s t m)
    (k u w : Nat) (hk : m ≤ k) (hw : 2*m ≤ w)
    (he : Edge s u w (s k)) : Edge t u w (t k) := by
  unfold Edge at *
  rw [← hag k hk, ← row_eq_of_agree s t m hag w hw]
  exact he

/-- Every finite match transfers with the same length and a start displaced
by at most m. The actual path is unchanged from time min(m,ell) onward. -/
theorem finite_edit_transport (s t : Nat → Bool) (m : Nat) (hag : AgreeFrom s t m)
    (path : Nat → Nat) (ell : Nat) (hpath : MatchesPrefix s path ell) :
    ∃ changed : Nat → Nat, MatchesPrefix t changed ell ∧
      changed 0 ≤ path 0+m ∧ path 0 ≤ changed 0+m ∧
      ∀ k, min m ell ≤ k → changed k = path k := by
  let r := min m ell
  have hrm : r ≤ m := Nat.min_le_left _ _
  have hre : r ≤ ell := Nat.min_le_right _ _
  have hl := prefix_lower_bound s path ell hpath r hre
  have hd := prefix_displacement s path ell hpath r hre
  obtain ⟨front, hj, hm, hlo, hhi⟩ := backward_prefix t r (path r) hl
  have htail : ∀ k, r ≤ k → k < ell → Edge t (path k) (path (k+1)) (t k) := by
    intro k hkr hk
    have hmk : m ≤ k := by dsimp [r] at hkr; omega
    have hw := prefix_lower_bound s path ell hpath (k+1) (by omega)
    exact tail_edge_transfer s t m hag k (path k) (path (k+1)) hmk (by omega) (hpath k hk)
  obtain ⟨changed, hzero, hm, hsame⟩ := splice_prefix t front path r ell hm hj htail
  exact ⟨changed, hm, by omega, by omega, hsame⟩

/-- The original Thue-Morse graph has no two-edge own-target match from zero. -/
theorem thue_zero_prefix_bound (path : Nat → Nat) (ell : Nat)
    (hz : path 0 = 0) (hm : MatchesPrefix ThueMorseBits.t path ell) : ell ≤ 1 := by
  by_cases hl : ell ≤ 1
  · exact hl
  · have hfirst := hm 0 (by omega)
    have hsecond := hm 1 (by omega)
    have hw : path 1 = 2 := by
      rcases hfirst with ⟨hroot, hfirst | hfirst⟩ <;> simp only [hz, Nat.zero_add] at * <;> omega
    rw [hw] at hsecond
    rcases hsecond with ⟨_, ⟨he, hc⟩ | ⟨he, hc⟩⟩
    · rw [he, SharpThueMorse.binary_row_eq] at hc
      simp at hc
    · rw [he, SharpThueMorse.binary_row_eq] at hc
      simp at hc

/-- Zero really has maximum one, including an actual one-edge witness. -/
theorem thue_zero_maximum :
    (∃ path : Nat → Nat, path 0 = 0 ∧ MatchesPrefix ThueMorseBits.t path 1) ∧
      ∀ path ell, path 0 = 0 → MatchesPrefix ThueMorseBits.t path ell → ell ≤ 1 := by
  refine ⟨⟨fun k => 2*k, rfl, ?_⟩, thue_zero_prefix_bound⟩
  intro k hk
  have hk0 : k = 0 := by omega
  subst k
  refine ⟨by decide, Or.inr ⟨rfl, ?_⟩⟩
  rw [SharpThueMorse.binary_row_eq]
  decide +kernel

/-- The sharp Thue-Morse bound survives m finite target edits with additive 8m
in its integral form, for every actual finite match from a positive start. -/
theorem finite_edit_thue_upper (s : Nat → Bool) (m : Nat)
    (hag : AgreeFrom s ThueMorseBits.t m) (path : Nat → Nat) (ell : Nat)
    (hv : 1 ≤ path 0) (hm : MatchesPrefix s path ell) :
    3*ell ≤ 8*path 0+8*m-1 := by
  obtain ⟨changed, hc, hle, _, _⟩ := finite_edit_transport s ThueMorseBits.t m hag path ell hm
  by_cases hz : changed 0 = 0
  · have hl := thue_zero_prefix_bound changed ell hz hc
    omega
  · have hl := SharpThueMorse.binary_path_prefix_bound changed ell (by omega) hc
    omega

/-- Transport the actual dyadic equality witnesses back into the finitely
edited graph; restricting the original start to exceed m keeps starts positive. -/
theorem finite_edit_thue_lower (s : Nat → Bool) (m : Nat)
    (hag : AgreeFrom s ThueMorseBits.t m) (n : Nat) (hn : m < 3*2^n-1) :
    ∃ path : Nat → Nat, 1 ≤ path 0 ∧ MatchesPrefix s path (8*2^n-3) ∧
      path 0 ≤ (3*2^n-1)+m ∧ (3*2^n-1) ≤ path 0+m ∧
      8*path 0 ≤ 3*(8*2^n-3)+8*m+1 := by
  obtain ⟨original, hstart, hm⟩ := sharp_family_prefix n
  have hrev : AgreeFrom ThueMorseBits.t s m := fun k hk => (hag k hk).symm
  obtain ⟨path, hm, hlow, hupp, _⟩ := finite_edit_transport ThueMorseBits.t s m hrev
    original (8*2^n-3) hm
  rw [hstart] at hlow hupp
  have hpow := Nat.two_pow_pos n
  exact ⟨path, by omega, hm, hlow, hupp, by omega⟩

/-- Existence of an actual length-ell matching prefix from a specified start. -/
def HasPrefix (s : Nat → Bool) (v ell : Nat) : Prop :=
  ∃ path : Nat → Nat, path 0 = v ∧ MatchesPrefix s path ell

/-- A maximum over all actual finite matching prefixes, including length zero. -/
def IsMaximumPrefix (s : Nat → Bool) (v ell : Nat) : Prop :=
  HasPrefix s v ell ∧ ∀ len, HasPrefix s v len → len ≤ ell

theorem bounded_prefix_maximum (s : Nat → Bool) (v bound : Nat)
    (hb : ∀ ell, HasPrefix s v ell → ell ≤ bound) :
    ∃ ell, IsMaximumPrefix s v ell := by
  classical
  induction bound with
  | zero =>
    exact ⟨0, ⟨fun _ => v, rfl, fun k hk => by omega⟩, hb⟩
  | succ bound ih =>
    by_cases hm : HasPrefix s v (bound+1)
    · exact ⟨bound+1, hm, hb⟩
    · apply ih
      intro ell he
      have hl := hb ell he
      have hne : ell ≠ bound+1 := by intro h; subst ell; exact hm he
      omega

/-- Every positive start in a finite edit of Thue-Morse has a genuine finite
maximum, and that maximum satisfies the same integral bound as every prefix. -/
theorem finite_edit_thue_maximum (s : Nat → Bool) (m : Nat)
    (hag : AgreeFrom s ThueMorseBits.t m) (v : Nat) (hv : 1 ≤ v) :
    ∃ ell, IsMaximumPrefix s v ell ∧ 3*ell ≤ 8*v+8*m-1 := by
  have hall : ∀ ell, HasPrefix s v ell → 3*ell ≤ 8*v+8*m-1 := by
    intro ell he
    obtain ⟨path, hzero, hm⟩ := he
    have hl := finite_edit_thue_upper s m hag path ell (by omega) hm
    simpa only [hzero] using hl
  obtain ⟨ell, hmax⟩ := bounded_prefix_maximum s v (8*v+8*m)
    (fun ell he => by have := hall ell he; omega)
  exact ⟨ell, hmax, hall ell hmax.1⟩

private theorem index_lt_two_pow (n : Nat) : n < 2^n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

/-- The transported near-sharp witnesses occur at arbitrarily large starts. -/
theorem finite_edit_thue_lower_above (s : Nat → Bool) (m : Nat)
    (hag : AgreeFrom s ThueMorseBits.t m) (requested : Nat) :
    ∃ (n : Nat) (path : Nat → Nat), requested ≤ path 0 ∧ 1 ≤ path 0 ∧
      MatchesPrefix s path (8*2^n-3) ∧
      path 0 ≤ (3*2^n-1)+m ∧ (3*2^n-1) ≤ path 0+m ∧
      8*path 0 ≤ 3*(8*2^n-3)+8*m+1 := by
  let n := m + requested + 1
  have hp : m + requested + 1 < 2^n := index_lt_two_pow n
  have hn : m < 3*2^n-1 := by omega
  obtain ⟨path, hpos, hm, hlow, hupp, hsharp⟩ := finite_edit_thue_lower s m hag n hn
  have hrequest : requested ≤ path 0 := by omega
  exact ⟨n, path, hrequest, hpos, hm, hlow, hupp, hsharp⟩

#print axioms prefix_lower_bound
#print axioms backward_prefix
#print axioms splice_prefix
#print axioms sharp_family_prefix
#print axioms finite_edit_transport
#print axioms thue_zero_maximum
#print axioms finite_edit_thue_upper
#print axioms finite_edit_thue_lower
#print axioms finite_edit_thue_maximum
#print axioms finite_edit_thue_lower_above

end FiniteEditStability
