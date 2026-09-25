import SamuelAlexanderResearch.QuantitativeAvoidance
import SamuelAlexanderResearch.SharpThueMorse
import SamuelAlexanderResearch.FiniteEditStability

/-!
# Phase shifts of the actual binary avoiding graph

The shifted target is `shift s a k = s (k + a)`. Its row coloring translates
by `2*a`, with graph destinations still required to be at least 2. Finite-path
transport accounts for the initial boundary. The endpoints prove the shifted
Thue--Morse upper bound and a dyadic existence family with a bounded start
interval; no exact shifted equality location is assumed.
-/

namespace PhaseShift

open BinaryAvoidance QuantitativeAvoidance

def shift (s : Nat → Bool) (a : Nat) : Nat → Bool := fun k => s (k + a)

theorem row_shift (s : Nat → Bool) (a w : Nat) :
    row (shift s a) w = row s (w + 2 * a) := by
  have hm : (w + 2 * a) % 2 = w % 2 := by omega
  have hd : (w + 2 * a) / 2 = w / 2 + a := by omega
  simp only [row, shift, hm, hd]

theorem edge_translate (s : Nat → Bool) (a u w : Nat) (label : Bool)
    (h : Edge (shift s a) u w label) :
    Edge s (u + 2 * a) (w + 2 * a) label := by
  obtain ⟨hw, (⟨hstep, hlabel⟩ | ⟨hstep, hlabel⟩)⟩ := h
  · exact ⟨by omega, Or.inl ⟨by omega, by simpa only [row_shift] using hlabel⟩⟩
  · exact ⟨by omega, Or.inr ⟨by omega, by simpa only [row_shift] using hlabel⟩⟩

/-- Translation is an equivalence away from the shifted graph's initial
destination boundary. The condition excludes the nonexistent edge 0 to 1. -/
theorem edge_translate_iff (s : Nat → Bool) (a u w : Nat) (label : Bool)
    (hw : 2 ≤ w) :
    Edge (shift s a) u w label ↔ Edge s (u + 2 * a) (w + 2 * a) label := by
  constructor
  · exact edge_translate s a u w label
  · rintro ⟨_, (⟨hstep, hlabel⟩ | ⟨hstep, hlabel⟩)⟩
    · exact ⟨hw, Or.inl ⟨by omega, by simpa only [row_shift] using hlabel⟩⟩
    · exact ⟨hw, Or.inr ⟨by omega, by simpa only [row_shift] using hlabel⟩⟩

theorem edge_subtract (s : Nat → Bool) (a u w : Nat) (label : Bool)
    (hu : 2 * a ≤ u) (hw : 2 * a + 2 ≤ w) (h : Edge s u w label) :
    Edge (shift s a) (u - 2 * a) (w - 2 * a) label := by
  apply (edge_translate_iff s a (u - 2 * a) (w - 2 * a) label (by omega)).mpr
  simpa only [Nat.sub_add_cancel hu, Nat.sub_add_cancel (by omega : 2 * a ≤ w)] using h

theorem prefix_translate (s : Nat → Bool) (a : Nat) (path : Nat → Nat) (ell : Nat)
    (hpath : MatchesPrefix (shift s a) path ell) :
    ∀ k, k < ell → Edge s (path k + 2 * a) (path (k + 1) + 2 * a) (s (k + a)) := by
  intro k hk
  exact edge_translate s a (path k) (path (k + 1)) (s (k + a)) (hpath k hk)

/-- Translate a shifted match and prepend the original target's first `a`
labels. The resulting start lies between the old start and that start plus `a`.
The displayed equality records the entire translated suffix. -/
theorem prepend_shifted_prefix (s : Nat → Bool) (a : Nat)
    (path : Nat → Nat) (ell : Nat) (hpath : MatchesPrefix (shift s a) path ell) :
    ∃ extended : Nat → Nat, path 0 ≤ extended 0 ∧ extended 0 ≤ path 0 + a ∧
      MatchesPrefix s extended (ell + a) ∧
      ∀ k, extended (k + a) = path k + 2 * a := by
  obtain ⟨front, hp, hprefix, hlow, hupp⟩ :=
    FiniteEditStability.backward_prefix s a (path 0 + 2 * a) (by omega)
  let tail := fun k => path (k - a) + 2 * a
  have hjoin : front a = tail a := by simpa [tail] using hp
  have htail : ∀ k, a ≤ k → k < ell + a →
      Edge s (tail k) (tail (k + 1)) (s k) := by
    intro k hka hk
    have he := prefix_translate s a path ell hpath (k - a) (by omega)
    have hnext : k + 1 - a = (k - a) + 1 := by omega
    have hindex : (k - a) + a = k := by omega
    simpa only [tail, hnext, hindex] using he
  obtain ⟨extended, hzero, hmatch, hlate⟩ :=
    FiniteEditStability.splice_prefix s front tail a (ell + a) hprefix hjoin htail
  refine ⟨extended, by omega, by omega, hmatch, ?_⟩
  intro k
  rw [hlate (k + a) (by omega)]
  simp [tail]

def subtractSuffix (path : Nat → Nat) (a : Nat) : Nat → Nat :=
  fun k => path (k + a) - 2 * a

/-- Cutting `a` edges and translating down by `2*a` produces a shifted match.
The finite own-target lower bound supplies nonnegative sources and destinations
at least 2, so natural subtraction does not create spurious edges. -/
theorem suffix_subtraction (s : Nat → Bool) (path : Nat → Nat) (ell a : Nat)
    (hpath : MatchesPrefix s path ell) (ha : a ≤ ell) :
    MatchesPrefix (shift s a) (subtractSuffix path a) (ell - a) := by
  intro k hk
  have hsource := FiniteEditStability.prefix_lower_bound s path ell hpath (k + a) (by omega)
  have hdest := FiniteEditStability.prefix_lower_bound s path ell hpath (k + a + 1) (by omega)
  have he := edge_subtract s a (path (k + a)) (path (k + a + 1)) (s (k + a))
    (by omega) (by omega) (hpath (k + a) (by omega))
  have hindex : k + 1 + a = k + a + 1 := by omega
  simpa only [subtractSuffix, shift, hindex] using he

theorem suffix_start_bounds (s : Nat → Bool) (path : Nat → Nat) (ell a : Nat)
    (hpath : MatchesPrefix s path ell) (ha : a ≤ ell) :
    path 0 - a ≤ subtractSuffix path a 0 ∧ subtractSuffix path a 0 ≤ path 0 := by
  have hdisplacement := FiniteEditStability.prefix_displacement s path ell hpath a ha
  have hlower := FiniteEditStability.prefix_lower_bound s path ell hpath a ha
  simp only [subtractSuffix, Nat.zero_add]
  omega

/-- The converse finite-path transport, with an explicit interval for its start.
Since these are naturals, `path 0 - a` is already truncated below at zero. -/
theorem cut_original_prefix (s : Nat → Bool) (path : Nat → Nat) (ell a : Nat)
    (hpath : MatchesPrefix s path ell) (ha : a ≤ ell) :
    ∃ shifted : Nat → Nat, path 0 - a ≤ shifted 0 ∧ shifted 0 ≤ path 0 ∧
      MatchesPrefix (shift s a) shifted (ell - a) :=
  ⟨subtractSuffix path a, (suffix_start_bounds s path ell a hpath ha).1,
    (suffix_start_bounds s path ell a hpath ha).2, suffix_subtraction s path ell a hpath ha⟩

/-- The actual shifted Thue--Morse graph inherits the sharp leading coefficient,
with the proved additive allowance `5*a` in the integer inequality. -/
theorem thueMorse_shift_prefix_bound (a : Nat) (path : Nat → Nat) (ell : Nat)
    (hv : 1 ≤ path 0) (hpath : MatchesPrefix (shift ThueMorseBits.t a) path ell) :
    3 * ell ≤ 8 * path 0 + 5 * a - 1 := by
  obtain ⟨extended, hlo, hhi, hmatch, _⟩ :=
    prepend_shifted_prefix ThueMorseBits.t a path ell hpath
  have hbound := SharpThueMorse.binary_path_prefix_bound extended (ell + a) (by omega) hmatch
  omega

/-- Each original exact dyadic family supplies a long shifted match at some
positive start in the displayed interval. No exact shifted maximum or exact
left-endpoint location is asserted. -/
theorem thueMorse_shift_dyadic_family (a n : Nat) (ha : a + 2 ≤ 3 * 2^n) :
    ∃ path : Nat → Nat, 3 * 2^n - a - 1 ≤ path 0 ∧ path 0 ≤ 3 * 2^n - 1 ∧
      1 ≤ path 0 ∧ MatchesPrefix (shift ThueMorseBits.t a) path (8 * 2^n - a - 3) := by
  obtain ⟨path, hzero, hmatch⟩ := FiniteEditStability.sharp_family_prefix n
  have hpow := Nat.two_pow_pos n
  have hlength : a ≤ 8 * 2^n - 3 := by omega
  obtain ⟨shifted, hlo, hhi, hshift⟩ :=
    cut_original_prefix ThueMorseBits.t path (8 * 2^n - 3) a hmatch hlength
  refine ⟨shifted, by omega, by omega, by omega, ?_⟩
  have heq : 8 * 2^n - 3 - a = 8 * 2^n - a - 3 := by omega
  simpa only [heq] using hshift

end PhaseShift

#print axioms PhaseShift.row_shift
#print axioms PhaseShift.edge_translate_iff
#print axioms PhaseShift.edge_subtract
#print axioms PhaseShift.prepend_shifted_prefix
#print axioms PhaseShift.suffix_subtraction
#print axioms PhaseShift.cut_original_prefix
#print axioms PhaseShift.thueMorse_shift_prefix_bound
#print axioms PhaseShift.thueMorse_shift_dyadic_family
