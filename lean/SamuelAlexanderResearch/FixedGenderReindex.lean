import SamuelAlexanderResearch.BirthOrder
import SamuelAlexanderResearch.FixedGenderLift
import SamuelAlexanderResearch.PositiveUnavoidability

/-!
# Reindexing retained fixed-gender populations

The vertices are the subtype of retained natural indices, not all ambient
indices. A birth-ordered enumeration is constructed by `BirthOrder`, finite
root and child covers are transported, and each reindexed edge receives the
fixed gender of its source. The actual binary positive theorem then gives
eventually-periodic realization inside the retained set.
-/

namespace FixedGenderReindex

open SpeciesBridge BinaryPopulation BinaryAvoidance FixedGenderLift

abbrev Retained (S : NatSet) := {x : Nat // S x}

def birth (S : NatSet) (x : Retained S) : Nat := x.val

/-- Filtering a finite ambient cover into the retained subtype never increases
its length. This preserves a numerical child cap as well as finiteness. -/
theorem retained_list_cover (S P : NatSet) (xs : List Nat)
    (hxs : ∀ x, S x → P x → x ∈ xs) :
    ∃ ys : List (Retained S), ys.length ≤ xs.length ∧
      ∀ x : Retained S, P x.val → x ∈ ys := by
  classical
  let retain : Nat → Option (Retained S) := fun x =>
    if hx : S x then some ⟨x, hx⟩ else none
  refine ⟨xs.filterMap retain, List.length_filterMap_le retain xs, ?_⟩
  intro x hx
  apply List.mem_filterMap.mpr
  refine ⟨x.val, hxs x.val x.property hx, ?_⟩
  simp [retain, x.property]

theorem retained_finiteCover (S P : NatSet)
    (hfinite : FiniteSupport (fun x => S x ∧ P x)) :
    BirthOrder.FiniteCover (fun x : Retained S => P x.val) := by
  obtain ⟨xs, hxs⟩ := hfinite
  obtain ⟨ys, _, hys⟩ := retained_list_cover S P xs (fun x hx hp => hxs x ⟨hx, hp⟩)
  exact ⟨ys, hys⟩

theorem retained_infinite (S : NatSet) (hinfinite : InfiniteSupport S) :
    BirthOrder.InfiniteVertices (Retained S) := by
  apply (BirthOrder.infiniteVertices_iff_not_finiteCover (Retained S)).mpr
  rintro ⟨xs, hxs⟩
  apply hinfinite
  refine ⟨xs.map Subtype.val, ?_⟩
  intro x hx
  exact List.mem_map.mpr ⟨⟨x, hx⟩, hxs ⟨x, hx⟩ trivial, rfl⟩

theorem retained_finiteSublevels (S : NatSet)
    (hdates : ∀ date, FiniteSupport (fun x => S x ∧ x < date)) :
    BirthOrder.FiniteSublevels (birth S) := by
  intro date
  apply retained_finiteCover S (fun x => x ≤ date)
  exact finiteSupport_mono (fun _ hx => ⟨hx.1, by omega⟩) (hdates (date + 1))

variable {E : Graph} {S : NatSet} {g : Nat → Bool} {cap : Nat}

/-- The ordered enumeration is derived from population data. It is not a
parameter of the positive theorem or a field of the population model. -/
noncomputable def enumeration (population : FixedGenderPopulation E S g cap) :
    BirthOrder.OrderedEnumeration (birth S) :=
  BirthOrder.orderedEnumeration (birth S) (retained_infinite S population.1)
    (retained_finiteSublevels S population.2.2.1)

noncomputable def vertex (population : FixedGenderPopulation E S g cap) (i : Nat) : Nat :=
  (enumeration population).toFun i |>.val

theorem vertex_retained (population : FixedGenderPopulation E S g cap) (i : Nat) :
    S (vertex population i) := (enumeration population).toFun i |>.property

theorem vertex_injective (population : FixedGenderPopulation E S g cap) (i j : Nat)
    (h : vertex population i = vertex population j) : i = j :=
  (enumeration population).injective i j (Subtype.ext h)

theorem vertex_surjective (population : FixedGenderPopulation E S g cap)
    (x : Nat) (hx : S x) : ∃ i, vertex population i = x := by
  obtain ⟨i, hi⟩ := (enumeration population).surjective ⟨x, hx⟩
  exact ⟨i, congrArg Subtype.val hi⟩

theorem vertex_nondecreasing (population : FixedGenderPopulation E S g cap)
    (i j : Nat) (hij : i ≤ j) : vertex population i ≤ vertex population j :=
  (enumeration population).nondecreasing i j hij

noncomputable def LabelledEdge (population : FixedGenderPopulation E S g cap) : LabelledGraph :=
  fun i j label => E (vertex population i) (vertex population j) ∧ g (vertex population i) = label

theorem forgetLabels_iff (population : FixedGenderPopulation E S g cap) (i j : Nat) :
    ForgetLabels (LabelledEdge population) i j ↔ E (vertex population i) (vertex population j) := by
  constructor
  · rintro ⟨_, he, _⟩
    exact he
  · intro he
    exact ⟨g (vertex population i), he, rfl⟩

/-- Reindexed roots are exactly retained induced roots. Deleted ambient indices
are never vertices of this enumeration and cannot create extra roots. -/
theorem root_iff (population : FixedGenderPopulation E S g cap) (i : Nat) :
    Root (ForgetLabels (LabelledEdge population)) i ↔
      Root (Induced E S) (vertex population i) := by
  constructor
  · intro hroot x hedge
    obtain ⟨j, hj⟩ := vertex_surjective population x hedge.1
    apply hroot j
    apply (forgetLabels_iff population j i).mpr
    simpa only [hj] using hedge.2.2
  · intro hroot j hedge
    exact hroot (vertex population j) ⟨vertex_retained population j,
      vertex_retained population i, (forgetLabels_iff population j i).mp hedge⟩

theorem finiteSupport_reindex (population : FixedGenderPopulation E S g cap)
    (P : NatSet) (hfinite : FiniteSupport (fun x => S x ∧ P x)) :
    FiniteSupport (fun i => P (vertex population i)) :=
  (enumeration population).finiteCover_pullback (fun x => P x.val)
    (retained_finiteCover S P hfinite)

theorem reindexed_child_cap (population : FixedGenderPopulation E S g cap) :
    ChildCap (ForgetLabels (LabelledEdge population)) Whole cap := by
  intro i _
  obtain ⟨xs, hlength, hxs⟩ := population.2.2.2.2.1
    (vertex population i) (vertex_retained population i)
  obtain ⟨ys, hylen, hys⟩ := retained_list_cover S
    (fun y => E (vertex population i) y) xs hxs
  refine ⟨ys.map (enumeration population).index, ?_, ?_⟩
  · simp only [List.length_map]
    omega
  · intro j _ hedge
    exact (enumeration population).pullback_cover
      (fun y => E (vertex population i) y.val) ys hys j
      ((forgetLabels_iff population i j).mp hedge)

theorem reindexed_children_finite (population : FixedGenderPopulation E S g cap) (i : Nat) :
    FiniteSupport (ForgetLabels (LabelledEdge population) i) := by
  obtain ⟨xs, _, hxs⟩ := reindexed_child_cap population i trivial
  exact ⟨xs, fun j he => hxs j trivial he⟩

theorem reindexed_strict (population : FixedGenderPopulation E S g cap) (i j : Nat)
    (hedge : ForgetLabels (LabelledEdge population) i j) : i < j := by
  apply (enumeration population).edges_increase
    (fun x y => E x.val y.val) (fun x y he => population.2.1 x.val y.val x.property y.property he) i j
  exact (forgetLabels_iff population i j).mp hedge

/-- Every local and global axiom of the binary natural-date population is
derived from the retained fixed-gender population. -/
theorem reindexed_binary_population (population : FixedGenderPopulation E S g cap) :
    BinaryNatPopulation (LabelledEdge population) := by
  refine ⟨?_, ⟨reindexed_strict population, finite_birthdate_prefix,
    reindexed_children_finite population, whole_infinite⟩, ?_, ?_⟩
  · intro i j a b ha hb
    exact ha.2.symm.trans hb.2
  · exact finiteSupport_mono (fun i hi => (root_iff population i).mp hi)
      (finiteSupport_reindex population (Root (Induced E S)) population.2.2.2.1)
  · intro j hnon label
    have hnon' : ¬ Root (Induced E S) (vertex population j) :=
      fun hroot => hnon ((root_iff population j).mpr hroot)
    obtain ⟨x, hx, he, hg⟩ := population.2.2.2.2.2
      (vertex population j) (vertex_retained population j) hnon' label
    obtain ⟨i, hi⟩ := vertex_surjective population x hx
    refine ⟨i, ?_⟩
    change E (vertex population i) (vertex population j) ∧ g (vertex population i) = label
    simpa only [hi] using And.intro he hg

def RealizesOn (E : Graph) (S : NatSet) (g target : Nat → Bool) : Prop :=
  ∃ path : Nat → Nat, ∀ k, S (path k) ∧ E (path k) (path (k + 1)) ∧ g (path k) = target k

theorem realizes_reindex_iff (population : FixedGenderPopulation E S g cap) (s : Nat → Bool) :
    Realizes (LabelledEdge population) s ↔ RealizesOn E S g s := by
  constructor
  · rintro ⟨path, hpath⟩
    exact ⟨fun k => vertex population (path k),
      fun k => ⟨vertex_retained population (path k), (hpath k).1, (hpath k).2⟩⟩
  · rintro ⟨path, hpath⟩
    let indices := fun k => (enumeration population).index ⟨path k, (hpath k).1⟩
    have hvertices : ∀ k, vertex population (indices k) = path k := by
      intro k
      exact congrArg Subtype.val ((enumeration population).toFun_index ⟨path k, (hpath k).1⟩)
    refine ⟨indices, ?_⟩
    intro k
    change E (vertex population (indices k)) (vertex population (indices (k + 1))) ∧
      g (vertex population (indices k)) = s k
    simpa only [hvertices] using (hpath k).2

/-- Unconditional positive realization, with neither a supplied enumeration
nor a supplied unavoidability theorem among its hypotheses. -/
theorem eventuallyPeriodic_realized (population : FixedGenderPopulation E S g cap)
    (s : Nat → Bool) (hperiodic : EventuallyPeriodic s) : RealizesOn E S g s :=
  (realizes_reindex_iff population s).mp
    (PositiveUnavoidability.eventuallyPeriodic_realized s hperiodic (LabelledEdge population)
      (reindexed_binary_population population))

def FixedGenderUnavoidable (cap : Nat) (s : Nat → Bool) : Prop :=
  ∀ E S g, FixedGenderPopulation E S g cap → RealizesOn E S g s

/-- The productive core supplies the negative half at cap 3, while the actual
positive theorem supplies the positive half through the subtype adapter. -/
theorem fixedGender_cap_three_classification (s : Nat → Bool) :
    FixedGenderUnavoidable 3 s ↔ EventuallyPeriodic s := by
  classical
  constructor
  · intro hunavoidable
    by_cases hperiodic : EventuallyPeriodic s
    · exact hperiodic
    · exact False.elim (core_avoids s hperiodic
        (hunavoidable (LiftEdge s) (Core s) gender (core_fixedGenderPopulation s)))
  · intro hperiodic E S g population
    exact eventuallyPeriodic_realized population s hperiodic

end FixedGenderReindex

#print axioms FixedGenderReindex.retained_list_cover
#print axioms FixedGenderReindex.enumeration
#print axioms FixedGenderReindex.root_iff
#print axioms FixedGenderReindex.reindexed_child_cap
#print axioms FixedGenderReindex.reindexed_binary_population
#print axioms FixedGenderReindex.realizes_reindex_iff
#print axioms FixedGenderReindex.eventuallyPeriodic_realized
#print axioms FixedGenderReindex.fixedGender_cap_three_classification
