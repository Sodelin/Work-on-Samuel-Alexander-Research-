import SamuelAlexanderResearch.FixedGenderReindex
import SamuelAlexanderResearch.PopulationReindex

/-!
The directed line graph of the actual binary avoiding population has permanent
source genders and exactly two children per vertex. A port records an original
edge; adjacency means that two original edges are consecutive. The unused port
0 would represent the nonexistent original edge 0 -> 1, and is not a vertex.
-/

namespace CapTwo

open SpeciesBridge BinaryAvoidance BinaryPopulation FixedGenderLift

/-- Positive ports represent every actual edge of `P_s`, independently of `s`. -/
def Vertices : NatSet := fun x => 1 ≤ x

def source (x : Nat) : Nat := x / 2
def target (x : Nat) : Nat := source x + 1 + x % 2

def gender (s : Nat → Bool) (x : Nat) : Bool :=
  if x % 2 = 0 then row s (target x) else !(row s (target x))

def Arc : Graph := fun x y => Vertices x ∧ Vertices y ∧ source y = target x

theorem target_lower (x : Nat) (hx : Vertices x) : 2 ≤ target x := by
  dsimp [Vertices] at hx
  dsimp [target, source]
  omega

theorem port_edge (s : Nat → Bool) (x : Nat) (hx : Vertices x) :
    BinaryAvoidance.Edge s (source x) (target x) (gender s x) := by
  refine ⟨target_lower x hx, ?_⟩
  by_cases heven : x % 2 = 0
  · exact Or.inl ⟨by simp [target, heven], by simp [gender, heven]⟩
  · have hodd : x % 2 = 1 := by omega
    exact Or.inr ⟨by simp [target, hodd, Nat.add_assoc], by simp [gender, heven]⟩

theorem arc_strict {x y : Nat} (h : Arc x y) : x < y := by
  have htarget := h.2.2
  dsimp [source, target] at htarget
  omega

theorem children_exactly (x y : Nat) (hx : Vertices x) :
    Arc x y ↔ y = 2 * target x ∨ y = 2 * target x + 1 := by
  have ht := target_lower x hx
  constructor
  · intro h
    have hs := h.2.2
    dsimp [source] at hs
    omega
  · intro h
    rcases h with rfl | rfl <;>
      refine ⟨hx, by dsimp [Vertices]; omega, ?_⟩ <;>
      dsimp [source] <;> omega

theorem exactly_two_children (x : Nat) (hx : Vertices x) :
    ∃ a b, a ≠ b ∧ Vertices a ∧ Vertices b ∧
      ∀ y, Arc x y ↔ y = a ∨ y = b := by
  have ht := target_lower x hx
  exact ⟨2 * target x, 2 * target x + 1, by omega,
    by dsimp [Vertices]; omega, by dsimp [Vertices]; omega,
    fun y => children_exactly x y hx⟩

theorem child_cap_two : ChildCap Arc Vertices 2 := by
  intro x hx
  refine ⟨[2 * target x, 2 * target x + 1], by simp, ?_⟩
  intro y _ he
  simpa using (children_exactly x y hx).mp he

/-- The two incoming ports are the original edges `(u-1) -> u` and
`(u-2) -> u`, where `u` is the source of the destination port. -/
theorem parents_exactly (x y : Nat) (hy : 2 ≤ source y) :
    Arc x y ↔ x = 2 * source y - 2 ∨ x = 2 * source y - 3 := by
  dsimp [Arc, Vertices, source, target] at *
  omega

/-- Every original labelled edge has a representing port of that same gender. -/
theorem edge_port (s : Nat → Bool) {u v : Nat} {b : Bool}
    (he : BinaryAvoidance.Edge s u v b) :
    ∃ x, Vertices x ∧ source x = u ∧ target x = v ∧ gender s x = b := by
  obtain ⟨hv, ⟨hstep, hlabel⟩ | ⟨hstep, hlabel⟩⟩ := he
  · refine ⟨2 * u, by dsimp [Vertices]; omega, ?_, ?_, ?_⟩
    · dsimp [source]; omega
    · dsimp [target, source]; omega
    · have hm : (2 * u) % 2 = 0 := by omega
      have ht : target (2 * u) = v := by dsimp [target, source]; omega
      simp [gender, hm, ht, hlabel]
  · refine ⟨2 * u + 1, by dsimp [Vertices]; omega, ?_, ?_, ?_⟩
    · dsimp [source]; omega
    · dsimp [target, source]; omega
    · have hm : (2 * u + 1) % 2 = 1 := by omega
      have ht : target (2 * u + 1) = v := by dsimp [target, source]; omega
      simp [gender, hm, ht, hlabel]

theorem incoming_gender (s : Nat → Bool) (y : Nat) (hy : Vertices y)
    (hsource : 2 ≤ source y) (b : Bool) :
    ∃ x, Vertices x ∧ Arc x y ∧ gender s x = b := by
  obtain ⟨u, he⟩ := BinaryPopulation.incoming_each_label s (source y) hsource b
  obtain ⟨x, hx, _, ht, hg⟩ := edge_port s he
  exact ⟨x, hx, ⟨hx, hy, ht.symm⟩, hg⟩

theorem root_iff (y : Nat) (hy : Vertices y) :
    Root (Induced Arc Vertices) y ↔ source y < 2 := by
  constructor
  · intro hroot
    by_cases h : 2 ≤ source y
    · obtain ⟨x, hx, he, _⟩ := incoming_gender (fun _ => false) y hy h false
      exact False.elim (hroot x ⟨hx, hy, he⟩)
    · omega
  · intro hsource x he
    have ht := target_lower x he.1
    have hs := he.2.2.2.2
    omega

theorem roots_exactly (y : Nat) :
    (Vertices y ∧ Root (Induced Arc Vertices) y) ↔ y = 1 ∨ y = 2 ∨ y = 3 := by
  constructor
  · rintro ⟨hy, hr⟩
    have hs := (root_iff y hy).mp hr
    dsimp [Vertices] at hy
    dsimp [source] at hs
    omega
  · intro h
    have hy : Vertices y := by dsimp [Vertices]; omega
    exact ⟨hy, (root_iff y hy).mpr (by dsimp [source]; omega)⟩

theorem vertices_infinite : InfiniteSupport Vertices := by
  intro hfinite
  obtain ⟨bound, hb⟩ := (finiteSupport_iff_bounded _).mp hfinite
  have h := hb (bound + 1) (by dsimp [Vertices]; omega)
  omega

/-- All population axioms refer to the retained positive ports. -/
theorem fixedGenderPopulation (s : Nat → Bool) :
    FixedGenderPopulation Arc Vertices (gender s) 2 := by
  refine ⟨vertices_infinite, fun _ _ _ _ h => arc_strict h, ?_, ?_, child_cap_two, ?_⟩
  · intro date
    exact (finiteSupport_iff_bounded _).mpr ⟨date, fun _ h => h.2⟩
  · refine ⟨[1, 2, 3], ?_⟩
    intro y hy
    simpa using (roots_exactly y).mp hy
  · intro y hy nonroot b
    have hs : 2 ≤ source y := by
      by_cases h : source y < 2
      · exact False.elim (nonroot ((root_iff y hy).mpr h))
      · omega
    exact incoming_gender s y hy hs b

/-- A line-graph path projects edge-for-edge, without a time or word shift. -/
theorem realizes_project (s word : Nat → Bool)
    (h : FixedGenderReindex.RealizesOn Arc Vertices (gender s) word) :
    BinaryPopulation.Realizes (BinaryAvoidance.Edge s) word := by
  obtain ⟨path, hp⟩ := h
  refine ⟨fun k => source (path k), ?_⟩
  intro k
  have he := port_edge s (path k) (hp k).1
  have ht := (hp k).2.1.2.2
  simpa only [ht, (hp k).2.2] using he

theorem realizes_lift (s word : Nat → Bool)
    (h : BinaryPopulation.Realizes (BinaryAvoidance.Edge s) word) :
    FixedGenderReindex.RealizesOn Arc Vertices (gender s) word := by
  classical
  obtain ⟨path, hp⟩ := h
  have ports := fun k => edge_port s (hp k)
  let lifted := fun k => Classical.choose (ports k)
  have hl := fun k => Classical.choose_spec (ports k)
  refine ⟨lifted, ?_⟩
  intro k
  refine ⟨(hl k).1, ⟨(hl k).1, (hl (k+1)).1, ?_⟩, (hl k).2.2.2⟩
  exact (hl (k+1)).2.1.trans (hl k).2.2.1.symm

theorem realizes_iff (s word : Nat → Bool) :
    FixedGenderReindex.RealizesOn Arc Vertices (gender s) word ↔
      BinaryPopulation.Realizes (BinaryAvoidance.Edge s) word :=
  ⟨realizes_project s word, realizes_lift s word⟩

theorem avoids_aperiodic (s : Nat → Bool) (hs : ¬ EventuallyPeriodic s) :
    ¬ FixedGenderReindex.RealizesOn Arc Vertices (gender s) s := by
  intro h
  exact BinaryPopulation.edge_avoids_aperiodic_target s hs (realizes_project s s h)

/-- Every non-eventually-periodic target has an actual fixed-gender cap-two
avoider with exactly three roots and exactly two children at every vertex. -/
theorem cap_two_avoider (s : Nat → Bool) (hs : ¬ EventuallyPeriodic s) :
    FixedGenderPopulation Arc Vertices (gender s) 2 ∧
    (∀ x, Vertices x → ∃ a b, a ≠ b ∧ Vertices a ∧ Vertices b ∧
      ∀ y, Arc x y ↔ y = a ∨ y = b) ∧
    (∀ y, (Vertices y ∧ Root (Induced Arc Vertices) y) ↔ y = 1 ∨ y = 2 ∨ y = 3) ∧
    ¬ FixedGenderReindex.RealizesOn Arc Vertices (gender s) s :=
  ⟨fixedGenderPopulation s, exactly_two_children, roots_exactly, avoids_aperiodic s hs⟩

theorem fixedGender_cap_two_classification (s : Nat → Bool) :
    FixedGenderReindex.FixedGenderUnavoidable 2 s ↔ EventuallyPeriodic s := by
  classical
  constructor
  · intro unavoidable
    by_cases hs : EventuallyPeriodic s
    · exact hs
    · exact False.elim (avoids_aperiodic s hs
        (unavoidable Arc Vertices (gender s) (fixedGenderPopulation s)))
  · intro hs E S g population
    exact FixedGenderReindex.eventuallyPeriodic_realized population s hs

/-- The fixed source gender is a functional numeric edge label on the actual
retained subtype, suitable for the existing graph-counting transport. -/
noncomputable def countedEdge (E : Graph) (S : NatSet) (g : Nat → Bool)
    (x y : FixedGenderReindex.Retained S) : Option Nat := by
  classical
  exact if E x.val y.val then some (bit (g x.val)) else none

theorem countedEdge_present (E : Graph) (S : NatSet) (g : Nat → Bool)
    (x y : FixedGenderReindex.Retained S) :
    (countedEdge E S g x y).isSome = true ↔ E x.val y.val := by
  classical
  simp [countedEdge]

theorem counted_root_iff (E : Graph) (S : NatSet) (g : Nat → Bool)
    (y : FixedGenderReindex.Retained S) :
    PopulationReindex.NoParents (countedEdge E S g) y ↔ Root (Induced E S) y.val := by
  classical
  constructor
  · intro hr x he
    have h := hr ⟨x, he.1⟩
    simp [countedEdge, he.2.2] at h
  · intro hr x
    have he : ¬ E x.val y.val := fun he => hr x.val ⟨x.property, y.property, he⟩
    simp [countedEdge, he]

/-- Every population in the existing retained fixed-gender model supplies
the actual graph, roots, and numeric child cap for subcritical counting. -/
noncomputable def presented {E : Graph} {S : NatSet} {g : Nat → Bool} {cap : Nat}
    (population : FixedGenderPopulation E S g cap) :
    PopulationReindex.PresentedPopulation (FixedGenderReindex.birth S) 2 cap where
  infinite := FixedGenderReindex.retained_infinite S population.1
  finite_sublevels := FixedGenderReindex.retained_finiteSublevels S population.2.2.1
  edge := countedEdge E S g
  birth_order := by
    intro x y he
    exact population.2.1 x.val y.val x.property y.property
      ((countedEdge_present E S g x y).mp he)
  label_valid := by
    classical
    intro x y label he
    by_cases hxy : E x.val y.val
    · have hlabel : bit (g x.val) = label := by simpa [countedEdge, hxy] using he
      rw [← hlabel]
      cases g x.val <;> decide
    · simp [countedEdge, hxy] at he
  roots_finite := by
    obtain ⟨roots, hroots⟩ := FixedGenderReindex.retained_finiteCover S
      (Root (Induced E S)) population.2.2.2.1
    exact ⟨roots, fun x hx => hroots x ((counted_root_iff E S g x).mp hx)⟩
  parent_of_label := by
    classical
    intro y nonroot label hlabel
    have hn : ¬ Root (Induced E S) y.val :=
      fun hr => nonroot ((counted_root_iff E S g y).mpr hr)
    let b : Bool := decide (label = 1)
    have hb : bit b = label := by
      have h : label = 0 ∨ label = 1 := by omega
      rcases h with rfl | rfl <;> rfl
    obtain ⟨x, hx, he, hg⟩ := population.2.2.2.2.2 y.val y.property hn b
    refine ⟨⟨x, hx⟩, ?_⟩
    simp only [countedEdge, if_pos he, hg, hb]
  children := by
    intro x
    obtain ⟨xs, hlen, hxs⟩ := population.2.2.2.2.1 x.val x.property
    obtain ⟨ys, hylen, hys⟩ := FixedGenderReindex.retained_list_cover S
      (fun y => E x.val y) xs hxs
    exact ⟨ys, Nat.le_trans hylen hlen,
      fun y he => hys y ((countedEdge_present E S g x y).mp he)⟩

theorem fixedGender_subcritical_impossible {E : Graph} {S : NatSet}
    {g : Nat → Bool} {cap : Nat} (population : FixedGenderPopulation E S g cap)
    (hcap : cap < 2) : False :=
  PopulationReindex.subcritical_impossible (presented population) hcap

theorem fixedGender_cap_one_impossible (E : Graph) (S : NatSet) (g : Nat → Bool) :
    ¬ FixedGenderPopulation E S g 1 :=
  fun population => fixedGender_subcritical_impossible population (by decide)

theorem fixedGenderPopulation_mono {E : Graph} {S : NatSet} {g : Nat → Bool}
    {a b : Nat} (population : FixedGenderPopulation E S g a) (hab : a ≤ b) :
    FixedGenderPopulation E S g b := by
  refine ⟨population.1, population.2.1, population.2.2.1, population.2.2.2.1,
    ?_, population.2.2.2.2.2⟩
  intro x hx
  obtain ⟨children, hlen, hchildren⟩ := population.2.2.2.2.1 x hx
  exact ⟨children, Nat.le_trans hlen hab, hchildren⟩

/-- Exact numerical threshold, including both the necessary nonperiodicity
and the impossibility of any infinite binary population below cap two. -/
theorem avoiding_population_exists_iff (cap : Nat) (s : Nat → Bool) :
    (∃ E S g, FixedGenderPopulation E S g cap ∧
      ¬ FixedGenderReindex.RealizesOn E S g s) ↔
      2 ≤ cap ∧ ¬ EventuallyPeriodic s := by
  constructor
  · rintro ⟨E, S, g, population, avoids⟩
    refine ⟨?_, ?_⟩
    · by_cases h : 2 ≤ cap
      · exact h
      · exact False.elim (fixedGender_subcritical_impossible population (by omega))
    · intro periodic
      exact avoids (FixedGenderReindex.eventuallyPeriodic_realized population s periodic)
  · rintro ⟨hcap, hs⟩
    exact ⟨Arc, Vertices, gender s,
      fixedGenderPopulation_mono (fixedGenderPopulation s) hcap, avoids_aperiodic s hs⟩

end CapTwo

#print axioms CapTwo.fixedGenderPopulation
#print axioms CapTwo.parents_exactly
#print axioms CapTwo.realizes_iff
#print axioms CapTwo.cap_two_avoider
#print axioms CapTwo.fixedGender_cap_two_classification
#print axioms CapTwo.presented
#print axioms CapTwo.fixedGender_subcritical_impossible
#print axioms CapTwo.avoiding_population_exists_iff
