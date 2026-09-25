import SamuelAlexanderResearch.PhaseShift

/-!
Exact finite frontiers and computable matching maxima for every shifted
Thue--Morse target, including start zero. This uses an explicit finite search
bound proved from the actual graph; it is not a sampled transition claim.
-/

namespace PhaseHeight

open BinaryAvoidance QuantitativeAvoidance FiniteEditStability PhaseShift

def Reaches (s : Nat → Bool) (v ell w : Nat) : Prop :=
  ∃ path : Nat → Nat, path 0 = v ∧ path ell = w ∧ MatchesPrefix s path ell

instance edgeDecidable (s : Nat → Bool) (u v : Nat) (b : Bool) : Decidable (Edge s u v b) := by
  unfold Edge
  infer_instance

def successors (s : Nat → Bool) (k x : Nat) : List Nat :=
  [x+1, x+2].filter (fun y => decide (Edge s x y (s k)))

theorem mem_successors (s : Nat → Bool) (k x y : Nat) :
    y ∈ successors s k x ↔ Edge s x y (s k) := by
  constructor
  · intro h
    have he := (List.mem_filter.mp h).2
    simpa using he
  · intro he
    apply List.mem_filter.mpr
    refine ⟨?_, by simpa using he⟩
    have hstep := he.2
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega

def frontier (s : Nat → Bool) (v : Nat) : Nat → List Nat
  | 0 => [v]
  | ell+1 => (frontier s v ell).flatMap (successors s ell)

theorem reaches_zero (s : Nat → Bool) (v w : Nat) : Reaches s v 0 w ↔ w = v := by
  constructor
  · rintro ⟨path, hv, hw, _⟩
    omega
  · intro h
    subst w
    exact ⟨fun _ => v, rfl, rfl, fun k hk => by omega⟩

theorem reaches_succ (s : Nat → Bool) (v ell w : Nat) :
    Reaches s v (ell+1) w ↔ ∃ u, Reaches s v ell u ∧ Edge s u w (s ell) := by
  constructor
  · rintro ⟨path, hv, hw, hm⟩
    refine ⟨path ell, ⟨path, hv, rfl, fun k hk => hm k (by omega)⟩, ?_⟩
    simpa only [hw] using hm ell (by omega)
  · rintro ⟨u, ⟨front, hv, hu, hm⟩, he⟩
    let path := fun k => if k ≤ ell then front k else w
    refine ⟨path, by simpa [path] using hv,
      by simp [path, show ¬ell+1 ≤ ell by omega], ?_⟩
    intro k hk
    by_cases hsmall : k < ell
    · simpa [path, show k ≤ ell by omega, show k+1 ≤ ell by omega] using hm k hsmall
    · have hk' : k = ell := by omega
      subst k
      simpa [path, hu, show ¬ell+1 ≤ ell by omega] using he

/-- Every listed endpoint, and only a listed endpoint, has an actual matching
path of the specified length. Duplicate list entries do not affect the iff. -/
theorem mem_frontier (s : Nat → Bool) (v ell w : Nat) :
    w ∈ frontier s v ell ↔ Reaches s v ell w := by
  induction ell generalizing w with
  | zero => simp [frontier, reaches_zero]
  | succ ell ih =>
    simp only [frontier, List.mem_flatMap, ih, mem_successors, reaches_succ]

theorem hasPrefix_iff_frontier_nonempty (s : Nat → Bool) (v ell : Nat) :
    HasPrefix s v ell ↔ frontier s v ell ≠ [] := by
  constructor
  · rintro ⟨path, hv, hm⟩ hnil
    have hmem := (mem_frontier s v ell (path ell)).mpr ⟨path, hv, rfl, hm⟩
    simp [hnil] at hmem
  · intro hnon
    cases he : frontier s v ell with
    | nil => exact False.elim (hnon he)
    | cons w rest =>
      have hmem : w ∈ frontier s v ell := by simp [he]
      obtain ⟨path, hv, _, hm⟩ := (mem_frontier s v ell w).mp hmem
      exact ⟨path, hv, hm⟩

theorem hasPrefix_mono (s : Nat → Bool) (v a b : Nat) (hab : a ≤ b)
    (h : HasPrefix s v b) : HasPrefix s v a := by
  obtain ⟨path, hv, hm⟩ := h
  exact ⟨path, hv, fun k hk => hm k (by omega)⟩

theorem hasPrefix_iff_le_maximum (s : Nat → Bool) (v height len : Nat)
    (hm : IsMaximumPrefix s v height) : HasPrefix s v len ↔ len ≤ height :=
  ⟨hm.2 len, fun h => hasPrefix_mono s v len height h hm.1⟩

/-- An executable maximum over the bounded set of matching lengths. -/
def boundedHeight (s : Nat → Bool) (v : Nat) : Nat → Nat
  | 0 => 0
  | bound+1 => if frontier s v (bound+1) = [] then boundedHeight s v bound else bound+1

theorem boundedHeight_isMaximum (s : Nat → Bool) (v bound : Nat)
    (hb : ∀ len, HasPrefix s v len → len ≤ bound) :
    IsMaximumPrefix s v (boundedHeight s v bound) := by
  induction bound with
  | zero =>
    change IsMaximumPrefix s v 0
    exact ⟨⟨fun _ => v, rfl, fun k hk => by omega⟩, hb⟩
  | succ bound ih =>
    by_cases hn : frontier s v (bound+1) = []
    · simp only [boundedHeight, if_pos hn]
      apply ih
      intro len hlen
      have hle := hb len hlen
      have hne : len ≠ bound+1 := by
        intro he
        subst len
        exact (hasPrefix_iff_frontier_nonempty s v (bound+1)).mp hlen hn
      omega
    · simp only [boundedHeight, if_neg hn]
      exact ⟨(hasPrefix_iff_frontier_nonempty s v (bound+1)).mpr hn, hb⟩

/-- A uniform, deliberately loose finite bound valid also at start zero. -/
theorem shifted_prefix_finite_bound (a v len : Nat)
    (hm : HasPrefix (shift ThueMorseBits.t a) v len) : len ≤ 8*(v+a)+1 := by
  obtain ⟨path, hv, hp⟩ := hm
  obtain ⟨extended, hlo, hhi, hext, _⟩ := prepend_shifted_prefix ThueMorseBits.t a path len hp
  by_cases hz : extended 0 = 0
  · have hb := thue_zero_prefix_bound extended (len+a) hz hext
    omega
  · have hb := SharpThueMorse.binary_path_prefix_bound extended (len+a) (by omega) hext
    omega

def height (a v : Nat) : Nat :=
  boundedHeight (shift ThueMorseBits.t a) v (8*(v+a)+1)

theorem height_isMaximum (a v : Nat) :
    IsMaximumPrefix (shift ThueMorseBits.t a) v (height a v) :=
  boundedHeight_isMaximum _ _ _ (fun len hm => shifted_prefix_finite_bound a v len hm)

theorem hasPrefix_iff_le_height (a v len : Nat) :
    HasPrefix (shift ThueMorseBits.t a) v len ↔ len ≤ height a v :=
  hasPrefix_iff_le_maximum _ _ _ _ (height_isMaximum a v)

theorem maximum_iff_height (a v len : Nat) :
    IsMaximumPrefix (shift ThueMorseBits.t a) v len ↔ len = height a v := by
  constructor
  · intro hm
    have hh := height_isMaximum a v
    exact Nat.le_antisymm (hh.2 len hm.1) (hm.2 _ hh.1)
  · intro he
    subst len
    exact height_isMaximum a v

end PhaseHeight

#print axioms PhaseHeight.mem_frontier
#print axioms PhaseHeight.boundedHeight_isMaximum
#print axioms PhaseHeight.height_isMaximum
#print axioms PhaseHeight.maximum_iff_height
