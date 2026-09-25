import Std
import Init.Data.Rat.Lemmas

/-!
Synthetic three-state cellular automaton: exact local parent certificates,
potential conservation, and a strict comparison with every valid static
two-label convex-hull certificate for the same local rule.

The full configuration update, finite-support charge strip, spaceship
obstruction, and an explicit nonempty two-cycle are proved below.
-/

namespace StatefulCA

abbrev Cell := Fin 3
abbrev Dir := Fin 6
abbrev Pattern := Dir → Cell

def dead : Cell := 0
def r : Cell := 1
def l : Cell := 2

-- Directions are predecessor locations relative to a target:
-- 0 W, 1 NW, 2 SW, 3 E, 4 NE, 5 SE.
def output (p : Pattern) : Cell :=
  if p 0 = r ∧ (p 1 = r ∨ p 2 = r) then l
  else if p 3 = l ∧ (p 4 = l ∨ p 5 = l) then r
  else dead

def selected (p : Pattern) (label : Bool) : Dir :=
  if output p = l then
    if label then (if p 1 = r then 1 else 2) else 0
  else if label then (if p 4 = l then 4 else 5) else 3

def dx (d : Dir) : Int := if d.val ≤ 2 then 1 else -1
def potential (q : Cell) : Int := if q = r then 1 else 0

-- The finite truth table has 3^6 = 729 local rows.
theorem every_live_row_has_two_parents :
    ∀ p : Pattern, output p ≠ dead →
      p (selected p false) ≠ dead ∧
      p (selected p true) ≠ dead ∧
      selected p false ≠ selected p true ∧
      (∀ label : Bool,
        dx (selected p label) =
          potential (p (selected p label)) - potential (output p)) := by
  intro p hp
  have hout : output p = l ∨ output p = r := by
    have h := (show ∀ c : Cell, c = dead ∨ c = r ∨ c = l from by decide +kernel) (output p)
    rcases h with h | h | h
    · exact False.elim (hp h)
    · exact Or.inr h
    · exact Or.inl h
  rcases hout with hl | hr
  · have first : p 0 = r ∧ (p 1 = r ∨ p 2 = r) := by
      unfold output at hl
      split at hl
      · assumption
      · split at hl <;> contradiction
    rcases first with ⟨hw, hn | hs⟩
    · simp [selected, hl, hw, hn, dead, r, l, dx, potential]
    · by_cases hn : p 1 = r
      · simp [selected, hl, hw, hn, dead, r, l, dx, potential]
      · change p 1 ≠ (1 : Cell) at hn
        simp [selected, hl, hw, hn, hs, dead, r, l, dx, potential]
  · have second : p 3 = l ∧ (p 4 = l ∨ p 5 = l) := by
      unfold output at hr
      split at hr
      · contradiction
      · split at hr
        · assumption
        · contradiction
    rcases second with ⟨he, hn | hs⟩
    · simp [selected, hr, he, hn, dead, r, l, dx, potential] <;> omega
    · by_cases hn : p 4 = l
      · simp [selected, hr, he, hn, dead, r, l, dx, potential] <;> omega
      · change p 4 ≠ (2 : Cell) at hn
        simp [selected, hr, he, hn, hs, dead, r, l, dx, potential] <;> omega

theorem charge_preserved (parentX childX : Int) (parent child : Cell)
    (step : childX - parentX = potential parent - potential child) :
    parentX + potential parent = childX + potential child := by
  omega

theorem selected_edge_charge (p : Pattern) (label : Bool) (parentX childX : Int)
    (live : output p ≠ dead)
    (step : childX - parentX = dx (selected p label)) :
    parentX + potential (p (selected p label)) =
      childX + potential (output p) := by
  have hlocal := (every_live_row_has_two_parents p live).2.2.2 label
  exact charge_preserved parentX childX _ _ (step.trans hlocal)

theorem finite_lifeline_charge (n : Nat) (pathX : Nat → Int)
    (pathQ : Nat → Cell) (rows : Nat → Pattern) (labels : Nat → Bool)
    (live : ∀ i, i < n → output (rows i) ≠ dead)
    (source : ∀ i, i < n → pathQ i = (rows i) (selected (rows i) (labels i)))
    (target : ∀ i, i < n → pathQ (i+1) = output (rows i))
    (step : ∀ i, i < n → pathX (i+1) - pathX i =
      dx (selected (rows i) (labels i))) :
    pathX 0 + potential (pathQ 0) = pathX n + potential (pathQ n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hprefix : pathX 0 + potential (pathQ 0) =
          pathX n + potential (pathQ n) :=
        ih (fun i hi => live i (by omega))
          (fun i hi => source i (by omega))
          (fun i hi => target i (by omega))
          (fun i hi => step i (by omega))
      have hlocal := selected_edge_charge (rows n) (labels n)
        (pathX n) (pathX (n+1)) (live n (by omega)) (step n (by omega))
      rw [← source n (by omega), ← target n (by omega)] at hlocal
      exact hprefix.trans hlocal

def northRow : Pattern := fun d => if d = 0 ∨ d = 1 then r else dead
def southRow : Pattern := fun d => if d = 0 ∨ d = 2 then r else dead

theorem northRow_output : output northRow = l := by decide +kernel
theorem southRow_output : output southRow = l := by decide +kernel

def FixedCert (a b : Dir → Prop) : Prop :=
  ∀ p : Pattern, output p ≠ dead →
    ∃ i j : Dir, i ≠ j ∧ a i ∧ b j ∧ p i ≠ dead ∧ p j ≠ dead

private theorem north_support :
    ∀ d : Dir, northRow d ≠ dead → d = 0 ∨ d = 1 := by
  decide +kernel

private theorem south_support :
    ∀ d : Dir, southRow d ≠ dead → d = 0 ∨ d = 2 := by
  decide +kernel

theorem static_east_options (a b : Dir → Prop) (cert : FixedCert a b) :
    (a 0 ∨ a 1) ∧ (a 0 ∨ a 2) ∧
    (b 0 ∨ b 1) ∧ (b 0 ∨ b 2) := by
  have north := cert northRow (by rw [northRow_output]; decide)
  have south := cert southRow (by rw [southRow_output]; decide)
  obtain ⟨ni, nj, _, nai, nbj, nlivei, nlivej⟩ := north
  obtain ⟨si, sj, _, sai, sbj, slivei, slivej⟩ := south
  have nA : a 0 ∨ a 1 := by
    rcases north_support ni nlivei with h | h <;> subst ni <;> simp_all
  have nB : b 0 ∨ b 1 := by
    rcases north_support nj nlivej with h | h <;> subst nj <;> simp_all
  have sA : a 0 ∨ a 2 := by
    rcases south_support si slivei with h | h <;> subst si <;> simp_all
  have sB : b 0 ∨ b 2 := by
    rcases south_support sj slivej with h | h <;> subst sj <;> simp_all
  exact ⟨nA, sA, nB, sB⟩

-- These are the actual parent-to-child vectors, not abstract tokens.
def xStep (d : Dir) : Rat := if d.val ≤ 2 then 1 else -1
def yStep (d : Dir) : Rat :=
  if d = 1 ∨ d = 4 then -1 else if d = 2 ∨ d = 5 then 1 else 0

def sum6 (w : Dir → Rat) : Rat :=
  w 0 + w 1 + w 2 + w 3 + w 4 + w 5

def weightedX (w : Dir → Rat) : Rat :=
  w 0 * xStep 0 + w 1 * xStep 1 + w 2 * xStep 2 +
  w 3 * xStep 3 + w 4 * xStep 4 + w 5 * xStep 5

def weightedY (w : Dir → Rat) : Rat :=
  w 0 * yStep 0 + w 1 * yStep 1 + w 2 * yStep 2 +
  w 3 * yStep 3 + w 4 * yStep 4 + w 5 * yStep 5

def InConv (D : Dir → Prop) (v : Rat × Rat) : Prop :=
  ∃ w : Dir → Rat,
    (∀ d, 0 ≤ w d) ∧
    (∀ d, w d ≠ 0 → D d) ∧
    sum6 w = 1 ∧
    weightedX w = v.1 ∧
    weightedY w = v.2

private theorem east_by_straight (D : Dir → Prop) (hd : D 0) :
    InConv D (1, 0) := by
  refine ⟨fun d => if d = 0 then 1 else 0, ?_, ?_, ?_, ?_, ?_⟩
  · intro d; by_cases h : d = 0 <;> simp [h] <;> decide +kernel
  · intro d hnonzero
    by_cases h : d = 0
    · simpa [h] using hd
    · simp [h] at hnonzero
  · decide +kernel
  · decide +kernel
  · decide +kernel

private theorem east_by_diagonals (D : Dir → Prop) (hn : D 1) (hs : D 2) :
    InConv D (1, 0) := by
  refine ⟨fun d => if d = 1 ∨ d = 2 then (1 : Rat) / 2 else 0, ?_, ?_, ?_, ?_, ?_⟩
  · intro d; by_cases h : d = 1 ∨ d = 2 <;> simp [h] <;> decide +kernel
  · intro d hnonzero
    by_cases h : d = 1 ∨ d = 2
    · rcases h with h | h
      · simpa [h] using hn
      · simpa [h] using hs
    · simp [h] at hnonzero
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem east_in_conv (D : Dir → Prop)
    (north : D 0 ∨ D 1) (south : D 0 ∨ D 2) :
    InConv D (1, 0) := by
  by_cases h : D 0
  · exact east_by_straight D h
  · exact east_by_diagonals D (north.resolve_left h) (south.resolve_left h)

/-- Every valid static two-label certificate admits the east unit vector in
both full convex hulls. Thus its hull intersection cannot exclude speed 1. -/
theorem no_static_east_improvement (a b : Dir → Prop) (cert : FixedCert a b) :
    InConv a (1, 0) ∧ InConv b (1, 0) := by
  obtain ⟨na, sa, nb, sb⟩ := static_east_options a b cert
  exact ⟨east_in_conv a na sa, east_in_conv b nb sb⟩

theorem any_static_convex_east_bound (D : Dir → Prop) (v : Rat × Rat)
    (inside : InConv D v) : v.1 ≤ 1 := by
  obtain ⟨w, nonneg, _, sum, xeq, _⟩ := inside
  have h3 := nonneg 3
  have h4 := nonneg 4
  have h5 := nonneg 5
  have h0 : xStep 0 = 1 := by decide +kernel
  have h1 : xStep 1 = 1 := by decide +kernel
  have h2 : xStep 2 = 1 := by decide +kernel
  have h3x : xStep 3 = -1 := by decide +kernel
  have h4x : xStep 4 = -1 := by decide +kernel
  have h5x : xStep 5 = -1 := by decide +kernel
  simp [weightedX, h0, h1, h2, h3x, h4x, h5x] at xeq
  simp [sum6] at sum
  grind

theorem optimal_static_east_bound (a b : Dir → Prop) (cert : FixedCert a b) :
    InConv a (1, 0) ∧ InConv b (1, 0) ∧
    (∀ v : Rat × Rat, InConv a v ∧ InConv b v → v.1 ≤ 1) := by
  obtain ⟨ha, hb⟩ := no_static_east_improvement a b cert
  exact ⟨ha, hb, fun v hv => any_static_convex_east_bound a v hv.1⟩

def Aligned (d : Dir) : Prop := d = 0 ∨ d = 3
def Diagonal (d : Dir) : Prop := d = 1 ∨ d = 2 ∨ d = 4 ∨ d = 5

theorem aligned_diagonal_certificate : FixedCert Aligned Diagonal := by
  intro p hp
  obtain ⟨ha, hb, hne, _⟩ := every_live_row_has_two_parents p hp
  refine ⟨selected p false, selected p true, hne, ?_, ?_, ha, hb⟩
  · by_cases hl : output p = l
    · simp [Aligned, selected, hl]
    · simp [Aligned, selected, hl]
  · by_cases hl : output p = l
    · by_cases h : p 1 = r <;> simp [Diagonal, selected, hl, h]
    · by_cases h : p 4 = l <;> simp [Diagonal, selected, hl, h]

theorem static_bound_is_attained_by_a_valid_certificate :
    InConv Aligned (1, 0) ∧ InConv Diagonal (1, 0) :=
  no_static_east_improvement Aligned Diagonal aligned_diagonal_certificate

theorem stateful_bound_strictly_less_than_static_east_bound : (0 : Rat) < 1 := by
  decide +kernel

abbrev Config := Int → Int → Cell

def rDomino : Config :=
  fun x y => if x = 0 ∧ (y = 0 ∨ y = 1) then r else dead

def lDomino : Config :=
  fun x y => if x = 1 ∧ (y = 0 ∨ y = 1) then l else dead

def neighborhood (c : Config) (x y : Int) : Pattern :=
  fun d =>
    if d = 0 then c (x-1) y
    else if d = 1 then c (x-1) (y+1)
    else if d = 2 then c (x-1) (y-1)
    else if d = 3 then c (x+1) y
    else if d = 4 then c (x+1) (y+1)
    else c (x+1) (y-1)

def evolve (c : Config) : Config := fun x y => output (neighborhood c x y)

private theorem live_phase (q : Cell) (hq : q ≠ dead) : q = l ∨ q = r := by
  have h := (show ∀ c : Cell, c = dead ∨ c = r ∨ c = l from by decide +kernel) q
  rcases h with h | h | h
  · exact False.elim (hq h)
  · exact Or.inr h
  · exact Or.inl h

private theorem output_l_west (p : Pattern) (h : output p = l) : p 0 = r := by
  unfold output at h
  split at h
  · exact ‹p 0 = r ∧ (p 1 = r ∨ p 2 = r)›.1
  · split at h <;> contradiction

private theorem output_r_east (p : Pattern) (h : output p = r) : p 3 = l := by
  unfold output at h
  split at h
  · contradiction
  · split at h
    · exact ‹p 3 = l ∧ (p 4 = l ∨ p 5 = l)›.1
    · contradiction

def ChargeBound (c : Config) (lo hi : Int) : Prop :=
  ∀ x y, c x y ≠ dead →
    lo ≤ x + potential (c x y) ∧ x + potential (c x y) ≤ hi

theorem evolve_preserves_charge_bound (c : Config) (lo hi : Int)
    (bound : ChargeBound c lo hi) : ChargeBound (evolve c) lo hi := by
  intro x y live
  let p := neighborhood c x y
  have hq : output p ≠ dead := live
  rcases live_phase (output p) hq with hl | hr
  · have hw : c (x-1) y = r := by
      have := output_l_west p hl
      simpa [p, neighborhood] using this
    have parent := bound (x-1) y (by rw [hw]; decide)
    change lo ≤ x + potential (output p) ∧ x + potential (output p) ≤ hi
    rw [hl]
    simp [hw, potential, r, l] at parent ⊢
    omega
  · have he : c (x+1) y = l := by
      have := output_r_east p hr
      simpa [p, neighborhood] using this
    have parent := bound (x+1) y (by rw [he]; decide)
    change lo ≤ x + potential (output p) ∧ x + potential (output p) ≤ hi
    rw [hr]
    simp [he, potential, r, l] at parent ⊢
    omega

def iterate (c : Config) : Nat → Config
  | 0 => c
  | n+1 => evolve (iterate c n)

theorem all_generations_in_initial_charge_strip (c : Config) (lo hi : Int)
    (bound : ChargeBound c lo hi) (n : Nat) :
    ChargeBound (iterate c n) lo hi := by
  induction n with
  | zero => exact bound
  | succ n ih => exact evolve_preserves_charge_bound _ lo hi ih

def FiniteSupport (c : Config) : Prop :=
  ∃ points : List (Int × Int),
    ∀ x y, c x y ≠ dead ↔ (x, y) ∈ points

theorem finite_support_has_extreme_charges (c : Config)
    (finite : FiniteSupport c) (nonempty : ∃ x y, c x y ≠ dead) :
    ∃ lo hi : Int, ChargeBound c lo hi ∧
      (∃ x y, c x y ≠ dead ∧ x + potential (c x y) = lo) ∧
      (∃ x y, c x y ≠ dead ∧ x + potential (c x y) = hi) := by
  obtain ⟨points, hpoints⟩ := finite
  let charge : Int × Int → Int := fun p => p.1 + potential (c p.1 p.2)
  let values := points.map charge
  have hne : values ≠ [] := by
    obtain ⟨x, y, hxy⟩ := nonempty
    have hmem : charge (x, y) ∈ values :=
      List.mem_map.mpr ⟨(x, y), (hpoints x y).mp hxy, rfl⟩
    exact List.ne_nil_of_mem hmem
  let lo := values.min hne
  let hi := values.max hne
  refine ⟨lo, hi, ?_, ?_, ?_⟩
  · intro x y hxy
    have hv : charge (x, y) ∈ values :=
      List.mem_map.mpr ⟨(x, y), (hpoints x y).mp hxy, rfl⟩
    exact ⟨List.min_le_of_mem hv, List.le_max_of_mem hv⟩
  · obtain ⟨⟨x, y⟩, hp, heq⟩ := List.mem_map.mp (List.min_mem hne)
    exact ⟨x, y, (hpoints x y).mpr hp, heq⟩
  · obtain ⟨⟨x, y⟩, hp, heq⟩ := List.mem_map.mp (List.max_mem hne)
    exact ⟨x, y, (hpoints x y).mpr hp, heq⟩

def translate (c : Config) (dx dy : Int) : Config :=
  fun x y => c (x-dx) (y-dy)

private theorem translated_value (c : Config) (dx dy x y : Int) :
    translate c dx dy (x+dx) (y+dy) = c x y := by
  simp [translate]

/-- A finite nonempty configuration cannot recur after any positive number of
steps with a nonzero horizontal translation. The rule-to-strip lemma above is
used for the entire trajectory; extremal initial charges make one recurrence
sufficient, so no asymptotic-limit argument or translation-equivariance lemma
is needed. -/
theorem no_horizontal_spaceship (c : Config) (period : Nat) (dx dy : Int)
    (finite : FiniteSupport c) (nonempty : ∃ x y, c x y ≠ dead)
    (recurs : iterate c period = translate c dx dy) : dx = 0 := by
  obtain ⟨lo, hi, bound, ⟨xmin, ymin, liveMin, minEq⟩,
    ⟨xmax, ymax, liveMax, maxEq⟩⟩ :=
    finite_support_has_extreme_charges c finite nonempty
  have futureBound := all_generations_in_initial_charge_strip c lo hi bound period
  have futureMin : (iterate c period) (xmin+dx) (ymin+dy) ≠ dead := by
    rw [recurs, translated_value]
    exact liveMin
  have futureMax : (iterate c period) (xmax+dx) (ymax+dy) ≠ dead := by
    rw [recurs, translated_value]
    exact liveMax
  have minBounds := futureBound (xmin+dx) (ymin+dy) futureMin
  have maxBounds := futureBound (xmax+dx) (ymax+dy) futureMax
  have minState : (iterate c period) (xmin+dx) (ymin+dy) = c xmin ymin := by
    rw [recurs, translated_value]
  have maxState : (iterate c period) (xmax+dx) (ymax+dy) = c xmax ymax := by
    rw [recurs, translated_value]
  rw [minState] at minBounds
  rw [maxState] at maxBounds
  omega

theorem rDomino_step : evolve rDomino = lDomino := by
  funext x y
  have hfirst :
      ((neighborhood rDomino x y 0 = r) ∧
        (neighborhood rDomino x y 1 = r ∨ neighborhood rDomino x y 2 = r)) ↔
      x = 1 ∧ (y = 0 ∨ y = 1) := by
    simp [neighborhood, rDomino, r, dead]
    omega
  have hsecond : ¬(neighborhood rDomino x y 3 = l ∧
      (neighborhood rDomino x y 4 = l ∨ neighborhood rDomino x y 5 = l)) := by
    intro h
    have hnoL (u v : Int) : rDomino u v ≠ l := by
      unfold rDomino
      split <;> decide
    exact hnoL (x+1) y (by simpa [neighborhood] using h.1)
  by_cases ht : x = 1 ∧ (y = 0 ∨ y = 1)
  · have hf := hfirst.mpr ht
    change output (neighborhood rDomino x y) = lDomino x y
    rw [show output (neighborhood rDomino x y) = l by
      simp only [output, if_pos hf]]
    simp [lDomino, ht]
  · have hf : ¬(neighborhood rDomino x y 0 = r ∧
        (neighborhood rDomino x y 1 = r ∨ neighborhood rDomino x y 2 = r)) :=
      fun h => ht (hfirst.mp h)
    change output (neighborhood rDomino x y) = lDomino x y
    rw [show output (neighborhood rDomino x y) = dead by
      simp only [output, if_neg hf, if_neg hsecond]]
    simp [lDomino, ht]

theorem lDomino_step : evolve lDomino = rDomino := by
  funext x y
  have hsecond :
      ((neighborhood lDomino x y 3 = l) ∧
        (neighborhood lDomino x y 4 = l ∨ neighborhood lDomino x y 5 = l)) ↔
      x = 0 ∧ (y = 0 ∨ y = 1) := by
    simp [neighborhood, lDomino, l, dead]
    omega
  have hfirst : ¬(neighborhood lDomino x y 0 = r ∧
      (neighborhood lDomino x y 1 = r ∨ neighborhood lDomino x y 2 = r)) := by
    intro h
    have hnoR (u v : Int) : lDomino u v ≠ r := by
      unfold lDomino
      split <;> decide
    exact hnoR (x-1) y (by simpa [neighborhood] using h.1)
  by_cases ht : x = 0 ∧ (y = 0 ∨ y = 1)
  · have hs := hsecond.mpr ht
    change output (neighborhood lDomino x y) = rDomino x y
    rw [show output (neighborhood lDomino x y) = r by
      simp only [output, if_neg hfirst, if_pos hs]]
    simp [rDomino, ht]
  · have hs : ¬(neighborhood lDomino x y 3 = l ∧
        (neighborhood lDomino x y 4 = l ∨ neighborhood lDomino x y 5 = l)) :=
      fun h => ht (hsecond.mp h)
    change output (neighborhood lDomino x y) = rDomino x y
    rw [show output (neighborhood lDomino x y) = dead by
      simp only [output, if_neg hfirst, if_neg hs]]
    simp [rDomino, ht]

theorem nontrivial_two_cycle :
    evolve rDomino = lDomino ∧ evolve lDomino = rDomino ∧
      rDomino 0 0 = r ∧ lDomino 1 0 = l ∧ rDomino ≠ lDomino := by
  refine ⟨rDomino_step, lDomino_step, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · intro h
    have := congrArg (fun c : Config => c 0 0) h
    have hr : rDomino 0 0 = r := by decide +kernel
    have hl : lDomino 0 0 = dead := by decide +kernel
    rw [hr, hl] at this
    contradiction

theorem rDomino_finite : FiniteSupport rDomino := by
  refine ⟨[(0, 0), (0, 1)], ?_⟩
  intro x y
  simp [rDomino, dead, r]
  omega

theorem rDomino_nonempty : ∃ x y, rDomino x y ≠ dead := by
  exact ⟨0, 0, by decide +kernel⟩

/-- The rule has a nonempty finite orbit, every valid fixed two-label
certificate includes east speed one in both rational convex hulls, yet
no finite nonempty orbit of the rule can recur with horizontal translation. -/
theorem stateful_rule_static_gap_and_global_obstruction :
    FixedCert Aligned Diagonal ∧
    (∀ a b, FixedCert a b →
      InConv a (1, 0) ∧ InConv b (1, 0) ∧
      (∀ v : Rat × Rat, InConv a v ∧ InConv b v → v.1 ≤ 1)) ∧
    (∀ c period dx dy, FiniteSupport c →
      (∃ x y, c x y ≠ dead) →
      iterate c period = translate c dx dy → dx = 0) ∧
    FiniteSupport rDomino ∧
    evolve rDomino = lDomino ∧ evolve lDomino = rDomino := by
  exact ⟨aligned_diagonal_certificate, optimal_static_east_bound,
    no_horizontal_spaceship, rDomino_finite, rDomino_step, lDomino_step⟩
end StatefulCA
