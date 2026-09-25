import SamuelAlexanderResearch.SpeciesRootCriterion
import SamuelAlexanderResearch.SpeciesGlobalIAP
import SamuelAlexanderResearch.FixedGenderReindex
import SamuelAlexanderResearch.PopulationReindex

namespace ProductiveCore

open SpeciesBridge SpeciesGlobalIAP BinaryPopulation

abbrev Induced := FixedGenderLift.Induced

def Core (E : Graph) : NatSet := fun v => InfiniteSupport (Descendant E v)

theorem descendant_mono {E F : Graph} (hEF : ∀ u v, E u v → F u v)
    {u v : Nat} (h : Descendant E u v) : Descendant F u v := by
  induction h with
  | edge he => exact .edge (hEF _ _ he)
  | snoc _ he ih => exact .snoc ih (hEF _ _ he)

theorem descendant_strict {E : Graph} (horder : ∀ u v, E u v → u < v)
    {u v : Nat} (h : Descendant E u v) : u < v := by
  induction h with
  | edge he => exact horder _ _ he
  | snoc _ he ih => exact Nat.lt_trans ih (horder _ _ he)

theorem descendant_first {E : Graph} {u v : Nat} (h : Descendant E u v) :
    ∃ child, E u child ∧ (v = child ∨ Descendant E child v) := by
  induction h with
  | edge he => exact ⟨_, he, Or.inl rfl⟩
  | snoc _ he ih =>
    obtain ⟨child, hc, h | h⟩ := ih
    · subst h
      exact ⟨_, hc, Or.inr (.edge he)⟩
    · exact ⟨child, hc, Or.inr (.snoc h he)⟩

theorem core_ancestrallyClosed (E : Graph) : AncestrallyClosed E (Core E) := by
  intro u v hv huv hfin
  exact hv (finiteSupport_mono (fun _ hvw => huv.trans hvw) hfin)

theorem core_convex (E : Graph) : Convex E (Core E) := by
  intro v _ hfuture
  obtain ⟨w, hw, hvw⟩ := hfuture
  exact core_ancestrallyClosed E v w hw hvw

theorem induced_descendant_of_closed {E : Graph} {S : NatSet}
    (hclosed : AncestrallyClosed E S) {u v : Nat}
    (h : Descendant E u v) (hv : S v) : Descendant (Induced E S) u v := by
  induction h with
  | edge he => exact .edge ⟨hclosed _ _ hv (.edge he), hv, he⟩
  | snoc _ he ih =>
    have hm := hclosed _ _ hv (.edge he)
    exact .snoc (ih hm) ⟨hm, hv, he⟩

theorem finite_cone {E : Graph} {v : Nat} (h : FiniteSupport (Descendant E v)) :
    FiniteSupport (fun w => w = v ∨ Descendant E v w) :=
  finiteSupport_union (finiteSupport_singleton v) h

theorem productive_exists (E : Graph) (horder : ∀ u v, E u v → u < v)
    (hroots : FiniteSupport (Root E)) : ∃ v, Core E v := by
  classical
  apply Classical.byContradiction
  intro hn
  have hfinite : ∀ v, FiniteSupport (Descendant E v) := by
    intro v
    exact Classical.byContradiction (fun hv => hn ⟨v, hv⟩)
  obtain ⟨r, hr⟩ := (finiteSupport_iff_bounded _).mp hroots
  obtain ⟨b, hb⟩ := PositiveUnavoidability.finite_union_bound
    (fun v w => w = v ∨ Descendant E v w) r
    (fun v _ => (finiteSupport_iff_bounded _).mp (finite_cone (hfinite v)))
  obtain ⟨v, hv, hcone⟩ := SpeciesRootCriterion.rootCovered_of_strict_birth_order E horder b
  exact Nat.lt_irrefl b (hb v (hr v hv) b hcone)

theorem productive_child (E : Graph) (hchildren : ∀ v, FiniteSupport (E v))
    (v : Nat) (hv : Core E v) : ∃ w, E v w ∧ Core E w := by
  classical
  apply Classical.byContradiction
  intro hn
  have hfinite : ∀ w, E v w → FiniteSupport (Descendant E w) := by
    intro w hw
    exact Classical.byContradiction (fun hp => hn ⟨w, hw, hp⟩)
  obtain ⟨n, hnchildren⟩ := (finiteSupport_iff_bounded _).mp (hchildren v)
  obtain ⟨b, hb⟩ := PositiveUnavoidability.finite_union_bound
    (fun w z => E v w ∧ (z = w ∨ Descendant E w z)) n (by
      intro w _
      by_cases hw : E v w
      · exact (finiteSupport_iff_bounded _).mp
          (finiteSupport_mono (fun _ hz => hz.2) (finite_cone (hfinite w hw)))
      · exact ⟨0, fun _ hz => False.elim (hw hz.1)⟩)
  apply hv
  apply (finiteSupport_iff_bounded _).mpr
  refine ⟨b, ?_⟩
  intro z hz
  obtain ⟨w, hw, hwz⟩ := descendant_first hz
  exact hb w (hnchildren w hw) z ⟨hw, hwz⟩

theorem core_infinite (E : Graph) (horder : ∀ u v, E u v → u < v)
    (hroots : FiniteSupport (Root E)) (hchildren : ∀ v, FiniteSupport (E v)) :
    InfiniteSupport (Core E) := by
  have arbitrarily_large : ∀ n, ∃ v, Core E v ∧ n ≤ v := by
    intro n
    induction n with
    | zero =>
      obtain ⟨v, hv⟩ := productive_exists E horder hroots
      exact ⟨v, hv, Nat.zero_le _⟩
    | succ n ih =>
      obtain ⟨v, hv, hn⟩ := ih
      obtain ⟨w, hw, hp⟩ := productive_child E hchildren v hv
      exact ⟨w, hp, by have := horder v w hw; omega⟩
  intro hfin
  obtain ⟨b, hb⟩ := (finiteSupport_iff_bounded _).mp hfin
  obtain ⟨v, hv, hlarge⟩ := arbitrarily_large b
  have := hb v hv
  omega

theorem productive_cofinite (E : Graph) (hiap : IAP E Whole) (v : Nat)
    (hv : Core E v) : FiniteSupport (fun w => ¬ Descendant E v w) := by
  rcases (iap_whole_iff E).mp hiap v with hf | hc
  · exact False.elim (hv hf)
  · exact hc

theorem core_inspecies (E : Graph) (horder : ∀ u v, E u v → u < v)
    (hroots : FiniteSupport (Root E)) (hchildren : ∀ v, FiniteSupport (E v))
    (hiap : IAP E Whole) : Inspecies E (Core E) := by
  classical
  refine ⟨⟨core_infinite E horder hroots hchildren, core_ancestrallyClosed E⟩, ?_⟩
  intro T _ hT v hv
  apply Classical.byContradiction
  intro hn
  apply hT.1
  exact finiteSupport_mono (fun w hw hvw => hn (hT.2 v w hw hvw))
    (productive_cofinite E hiap v hv)

theorem core_induced_inspecies (E : Graph) (horder : ∀ u v, E u v → u < v)
    (hroots : FiniteSupport (Root E)) (hchildren : ∀ v, FiniteSupport (E v))
    (hiap : IAP E Whole) : Inspecies (Induced E (Core E)) (Core E) := by
  have h := core_inspecies E horder hroots hchildren hiap
  refine ⟨⟨h.1.1, ?_⟩, ?_⟩
  · intro u v hv huv
    exact h.1.2 u v hv (descendant_mono (fun _ _ he => he.2.2) huv)
  · intro T hsub hT
    apply h.2 T hsub
    refine ⟨hT.1, ?_⟩
    intro u v hv huv
    exact hT.2 u v hv
      (induced_descendant_of_closed (core_ancestrallyClosed E) huv (hsub v hv))

/-- The population axioms on an actual retained subset. Birth dates are the
original natural indices; deleted indices are not vertices. -/
structure PopulationOn (E : LabelledGraph) (S : NatSet) : Prop where
  unique : UniqueLabels E
  infinite : InfiniteSupport S
  order : ∀ u v, S u → S v → ForgetLabels E u v → u < v
  children : ∀ u, S u → FiniteSupport (fun v => S v ∧ ForgetLabels E u v)
  roots : FiniteSupport (fun v => S v ∧ Root (Induced (ForgetLabels E) S) v)
  parents : ∀ v, S v → ¬ Root (Induced (ForgetLabels E) S) v →
    ∀ b, ∃ u, S u ∧ E u v b

theorem whole_population {E : LabelledGraph} (p : BinaryNatPopulation E) :
    PopulationOn E Whole := by
  refine ⟨p.1, whole_infinite, fun u v _ _ => p.2.1.1 u v, ?_, ?_, ?_⟩
  · intro u _
    exact finiteSupport_mono (fun _ hv => hv.2) (p.2.1.2.2.1 u)
  · apply finiteSupport_mono (T := Root (ForgetLabels E)) _ p.2.2.1
    intro v hv u he
    exact hv.2 u ⟨trivial, trivial, he⟩
  · intro v _ hn b
    have hn' : ¬ Root (ForgetLabels E) v := fun hr => hn (fun u he => hr u he.2.2)
    obtain ⟨u, hu⟩ := p.2.2.2 v hn' b
    exact ⟨u, trivial, hu⟩

theorem closed_root_iff {E : Graph} {S : NatSet} (hclosed : AncestrallyClosed E S)
    {v : Nat} (hv : S v) : Root (Induced E S) v ↔ Root E v := by
  constructor
  · intro hr u he
    exact hr u ⟨hclosed u v hv (.edge he), hv, he⟩
  · intro hr u he
    exact hr u he.2.2

theorem core_population {E : LabelledGraph} (p : BinaryNatPopulation E) :
    PopulationOn E (Core (ForgetLabels E)) := by
  let G := ForgetLabels E
  refine ⟨p.1, core_infinite G p.2.1.1 p.2.2.1 p.2.1.2.2.1,
    fun u v _ _ => p.2.1.1 u v, ?_, ?_, ?_⟩
  · intro u _
    exact finiteSupport_mono (fun _ hv => hv.2) (p.2.1.2.2.1 u)
  · exact finiteSupport_mono
      (fun _ hv => (closed_root_iff (core_ancestrallyClosed G) hv.1).mp hv.2) p.2.2.1
  · intro v hv hn b
    have hn' : ¬ Root G v := fun hr => hn ((closed_root_iff (core_ancestrallyClosed G) hv).mpr hr)
    obtain ⟨u, hu⟩ := p.2.2.2 v hn' b
    exact ⟨u, core_ancestrallyClosed G u v hv (.edge ⟨b, hu⟩), hu⟩

def Restrict (E : LabelledGraph) (S : NatSet) : LabelledGraph :=
  fun u v b => S u ∧ S v ∧ E u v b

theorem restriction_preserves_paths (E : LabelledGraph) (S : NatSet) (s : Nat → Bool) :
    Realizes (Restrict E S) s → Realizes E s := by
  rintro ⟨path, hp⟩
  exact ⟨path, fun k => (hp k).2.2⟩

theorem restriction_preserves_avoidance (E : LabelledGraph) (S : NatSet) (s : Nat → Bool)
    (h : ¬ Realizes E s) : ¬ Realizes (Restrict E S) s :=
  fun hs => h (restriction_preserves_paths E S s hs)

theorem core_preserves_child_cap (E : Graph) (d : Nat)
    (h : FixedGenderLift.ChildCap E Whole d) : FixedGenderLift.ChildCap E (Core E) d := by
  intro u _
  obtain ⟨xs, hlen, hxs⟩ := h u trivial
  exact ⟨xs, hlen, fun v _ he => hxs v trivial he⟩

noncomputable def enumeration {E : LabelledGraph} {S : NatSet} (p : PopulationOn E S) :
    BirthOrder.OrderedEnumeration (FixedGenderReindex.birth S) :=
  BirthOrder.orderedEnumeration _ (FixedGenderReindex.retained_infinite S p.infinite)
    (FixedGenderReindex.retained_finiteSublevels S
      (fun n => finiteSupport_mono (fun _ h => h.2) (finite_birthdate_prefix n)))

noncomputable def vertex {E : LabelledGraph} {S : NatSet} (p : PopulationOn E S) (i : Nat) : Nat :=
  ((enumeration p).toFun i).val

theorem vertex_mem {E : LabelledGraph} {S : NatSet} (p : PopulationOn E S) (i : Nat) :
    S (vertex p i) := ((enumeration p).toFun i).property

theorem vertex_surjective {E : LabelledGraph} {S : NatSet} (p : PopulationOn E S)
    (v : Nat) (hv : S v) : ∃ i, vertex p i = v := by
  obtain ⟨i, hi⟩ := (enumeration p).surjective ⟨v, hv⟩
  exact ⟨i, congrArg Subtype.val hi⟩

noncomputable def reindexed {E : LabelledGraph} {S : NatSet} (p : PopulationOn E S) :
    LabelledGraph := fun i j b => E (vertex p i) (vertex p j) b

theorem reindexed_root_iff {E : LabelledGraph} {S : NatSet} (p : PopulationOn E S) (i : Nat) :
    Root (ForgetLabels (reindexed p)) i ↔ Root (Induced (ForgetLabels E) S) (vertex p i) := by
  constructor
  · intro hr u hu
    obtain ⟨j, hj⟩ := vertex_surjective p u hu.1
    apply hr j
    change ForgetLabels E (vertex p j) (vertex p i)
    simpa only [hj] using hu.2.2
  · intro hr j he
    exact hr (vertex p j) ⟨vertex_mem p j, vertex_mem p i, he⟩

theorem reindex_finite {E : LabelledGraph} {S : NatSet} (p : PopulationOn E S)
    (P : NatSet) (h : FiniteSupport (fun v => S v ∧ P v)) :
    FiniteSupport (fun i => P (vertex p i)) :=
  (enumeration p).finiteCover_pullback (fun v => P v.val)
    (FixedGenderReindex.retained_finiteCover S P h)

theorem reindexed_population {E : LabelledGraph} {S : NatSet} (p : PopulationOn E S) :
    BinaryNatPopulation (reindexed p) := by
  refine ⟨?_, ⟨?_, finite_birthdate_prefix, ?_, whole_infinite⟩, ?_, ?_⟩
  · intro i j a b ha hb
    exact p.unique _ _ _ _ ha hb
  · intro i j he
    exact (enumeration p).edges_increase (fun u v => ForgetLabels E u.val v.val)
      (fun u v h => p.order u.val v.val u.property v.property h) i j he
  · intro i
    exact reindex_finite p (ForgetLabels E (vertex p i)) (p.children _ (vertex_mem p i))
  · exact finiteSupport_mono (fun i hi => (reindexed_root_iff p i).mp hi)
      (reindex_finite p (Root (Induced (ForgetLabels E) S)) p.roots)
  · intro j hn b
    have hn' := fun h => hn ((reindexed_root_iff p j).mpr h)
    obtain ⟨u, hu, he⟩ := p.parents _ (vertex_mem p j) hn' b
    obtain ⟨i, hi⟩ := vertex_surjective p u hu
    exact ⟨i, by change E (vertex p i) (vertex p j) b; simpa only [hi] using he⟩

theorem reindexed_realizes_iff {E : LabelledGraph} {S : NatSet} (p : PopulationOn E S)
    (s : Nat → Bool) : Realizes (reindexed p) s ↔ Realizes (Restrict E S) s := by
  constructor
  · rintro ⟨path, hp⟩
    exact ⟨fun k => vertex p (path k), fun k =>
      ⟨vertex_mem p _, vertex_mem p _, hp k⟩⟩
  · rintro ⟨path, hp⟩
    let indices := fun k => (enumeration p).index ⟨path k, (hp k).1⟩
    have hvertices : ∀ k, vertex p (indices k) = path k := by
      intro k
      exact congrArg Subtype.val ((enumeration p).toFun_index ⟨path k, (hp k).1⟩)
    refine ⟨indices, ?_⟩
    intro k
    change E (vertex p (indices k)) (vertex p (indices (k + 1))) (s k)
    simpa only [hvertices] using (hp k).2.2

theorem reindexed_child_cap {E : LabelledGraph} {S : NatSet} (p : PopulationOn E S)
    (d : Nat) (hcap : FixedGenderLift.ChildCap (ForgetLabels E) S d) :
    FixedGenderLift.ChildCap (ForgetLabels (reindexed p)) Whole d := by
  intro i _
  obtain ⟨xs, hlen, hxs⟩ := hcap _ (vertex_mem p i)
  obtain ⟨ys, hylen, hys⟩ := FixedGenderReindex.retained_list_cover S
    (ForgetLabels E (vertex p i)) xs hxs
  refine ⟨ys.map (enumeration p).index, ?_, ?_⟩
  · simpa only [List.length_map] using Nat.le_trans hylen hlen
  · intro j _ he
    exact (enumeration p).pullback_cover (fun v => ForgetLabels E (vertex p i) v.val) ys hys j he

theorem descendant_map {E F : Graph} (f : Nat → Nat)
    (hedge : ∀ u v, E u v → F (f u) (f v)) {u v : Nat}
    (h : Descendant E u v) : Descendant F (f u) (f v) := by
  induction h with
  | edge he => exact .edge (hedge _ _ he)
  | snoc _ he ih => exact .snoc ih (hedge _ _ he)

noncomputable def indexOf {E : LabelledGraph} {S : NatSet} (p : PopulationOn E S) (v : Nat) : Nat := by
  classical
  exact if hv : S v then (enumeration p).index ⟨v, hv⟩ else 0

theorem vertex_indexOf {E : LabelledGraph} {S : NatSet} (p : PopulationOn E S)
    (v : Nat) (hv : S v) : vertex p (indexOf p v) = v := by
  classical
  simp only [indexOf, dif_pos hv]
  exact congrArg Subtype.val ((enumeration p).toFun_index ⟨v, hv⟩)

theorem indexOf_vertex {E : LabelledGraph} {S : NatSet} (p : PopulationOn E S)
    (i : Nat) : indexOf p (vertex p i) = i := by
  apply (enumeration p).injective
  apply Subtype.ext
  exact vertex_indexOf p _ (vertex_mem p i)

theorem reindexed_descendant_iff_of_closed {E : LabelledGraph} {S : NatSet}
    (p : PopulationOn E S) (hclosed : AncestrallyClosed (ForgetLabels E) S) (i j : Nat) :
    Descendant (ForgetLabels (reindexed p)) i j ↔
      Descendant (ForgetLabels E) (vertex p i) (vertex p j) := by
  constructor
  · exact descendant_map (E := ForgetLabels (reindexed p)) (F := ForgetLabels E)
      (vertex p) (fun _ _ h => h)
  · intro h
    have hd := induced_descendant_of_closed hclosed h (vertex_mem p j)
    have hm := descendant_map (F := ForgetLabels (reindexed p)) (indexOf p) (by
      intro u v he
      change ForgetLabels E (vertex p (indexOf p u)) (vertex p (indexOf p v))
      simpa only [vertex_indexOf p u he.1, vertex_indexOf p v he.2.1] using he.2.2) hd
    simpa only [indexOf_vertex] using hm

theorem reindexed_core_whole_inspecies {E : LabelledGraph} (p : BinaryNatPopulation E)
    (hiap : IAP (ForgetLabels E) Whole) :
    Inspecies (ForgetLabels (reindexed (core_population p))) Whole := by
  apply (whole_inspecies_iff_cofinite_descendants _).mpr
  intro i
  let q := core_population p
  have hf := productive_cofinite (ForgetLabels E) hiap (vertex q i) (vertex_mem q i)
  apply finiteSupport_mono (T := fun j => ¬ Descendant (ForgetLabels E) (vertex q i) (vertex q j))
  · intro j hj hd
    exact hj ((reindexed_descendant_iff_of_closed q (core_ancestrallyClosed _) i j).mpr hd)
  · exact reindex_finite q _ (finiteSupport_mono (fun _ h => h.2) hf)

theorem cofinite_descendants_specieslike (E : Graph) (hcofinite : CofiniteDescendants E) :
    Specieslike E Whole := by
  classical
  refine ⟨⟨⟨0, trivial⟩, ?_⟩, (iap_whole_iff E).mpr (fun v => Or.inr (hcofinite v)), whole_convex E⟩
  intro u v _ _
  obtain ⟨b, hb⟩ := (finiteSupport_iff_bounded _).mp
    (finiteSupport_union (hcofinite u) (hcofinite v))
  have hu : Descendant E u b := Classical.byContradiction
    (fun hn => Nat.lt_irrefl b (hb b (Or.inl hn)))
  have hv : Descendant E v b := Classical.byContradiction
    (fun hn => Nat.lt_irrefl b (hb b (Or.inr hn)))
  exact .trans hu.weakReach_whole hv.weakReach_whole.symm

theorem reindexed_core_whole_specieslike {E : LabelledGraph} (p : BinaryNatPopulation E)
    (hiap : IAP (ForgetLabels E) Whole) :
    Specieslike (ForgetLabels (reindexed (core_population p))) Whole :=
  cofinite_descendants_specieslike _
    ((whole_inspecies_iff_cofinite_descendants _).mp (reindexed_core_whole_inspecies p hiap))

theorem infinite_path_vertices_productive (E : Graph) (horder : ∀ u v, E u v → u < v)
    (path : Nat → Nat) (hedges : ∀ k, E (path k) (path (k + 1))) : ∀ k, Core E (path k) := by
  have lower : ∀ k n, path k + n ≤ path (k + n) := by
    intro k n
    induction n with
    | zero => simp
    | succ n ih =>
      have h := horder _ _ (hedges (k + n))
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using
        (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt ih h))
  have reaches : ∀ k n, Descendant E (path k) (path (k + n + 1)) := by
    intro k n
    induction n with
    | zero => simpa using Descendant.edge (hedges k)
    | succ n ih =>
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using Descendant.snoc ih (hedges (k + n + 1))
  intro k hf
  obtain ⟨b, hb⟩ := (finiteSupport_iff_bounded _).mp hf
  have hsmall := hb _ (reaches k b)
  have hlarge := lower k (b + 1)
  simp only [Nat.add_assoc] at hsmall
  omega

/-- Pruning preserves the entire infinite word language, not merely one
avoided target. No assertion of finite-path preservation is made. -/
theorem reindexed_core_language_iff {E : LabelledGraph} (p : BinaryNatPopulation E)
    (s : Nat → Bool) : Realizes (reindexed (core_population p)) s ↔ Realizes E s := by
  rw [reindexed_realizes_iff]
  constructor
  · exact restriction_preserves_paths E _ s
  · rintro ⟨path, hp⟩
    have hcore := infinite_path_vertices_productive (ForgetLabels E) p.2.1.1 path
      (fun k => ⟨s k, hp k⟩)
    exact ⟨path, fun k => ⟨hcore k, hcore (k + 1), hp k⟩⟩

/-- Full pruning statement: an actual eligible core, an inspecies, unchanged
child cap, and every avoided word still avoided after the constructed reindexing. -/
theorem productive_core_theorem {E : LabelledGraph} (p : BinaryNatPopulation E)
    (hiap : IAP (ForgetLabels E) Whole) (d : Nat)
    (hcap : FixedGenderLift.ChildCap (ForgetLabels E) Whole d) :
    BinaryNatPopulation (reindexed (core_population p)) ∧
    Inspecies (Induced (ForgetLabels E) (Core (ForgetLabels E))) (Core (ForgetLabels E)) ∧
    FixedGenderLift.ChildCap (ForgetLabels (reindexed (core_population p))) Whole d ∧
    ∀ s, ¬ Realizes E s → ¬ Realizes (reindexed (core_population p)) s := by
  refine ⟨reindexed_population _,
    core_induced_inspecies _ p.2.1.1 p.2.2.1 p.2.1.2.2.1 hiap,
    reindexed_child_cap _ d (core_preserves_child_cap _ d hcap), ?_⟩
  intro s hs hp
  exact restriction_preserves_avoidance E _ s hs
    ((reindexed_realizes_iff (core_population p) s).mp hp)

def DescendantClosed (E : Graph) (S : NatSet) : Prop :=
  ∀ u v, S u → Descendant E u v → S v

theorem weakReach_mono_set {E : Graph} {S T : NatSet} (hsub : ∀ v, S v → T v)
    {u v : Nat} (h : WeakReach E S u v) : WeakReach E T u v := by
  induction h with
  | refl hu => exact .refl (hsub _ hu)
  | edge hu hv he => exact .edge (hsub _ hu) (hsub _ hv) he
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

theorem descendant_weakReach_convex {E : Graph} {S : NatSet} (hconv : Convex E S)
    {u v : Nat} (h : Descendant E u v) (hu : S u) (hv : S v) : WeakReach E S u v := by
  induction h with
  | edge he => exact .edge hu hv (Or.inl he)
  | snoc hd he ih =>
    have hm := hconv _ ⟨u, hu, hd⟩ ⟨_, hv, .edge he⟩
    exact .trans (ih hm) (.edge hm hv (Or.inl he))

/-- Convex closure needed to add one descendant, without adding vertices that
have no ancestor in the old set. Every added vertex is at most `w`. -/
def Extension (E : Graph) (S : NatSet) (w : Nat) : NatSet := fun v =>
  S v ∨ ((∃ a, S a ∧ Descendant E a v) ∧ (v = w ∨ Descendant E v w))

theorem extension_convex (E : Graph) (S : NatSet) (w : Nat) (hS : Convex E S) :
    Convex E (Extension E S w) := by
  intro v ha hb
  obtain ⟨a, ha, hav⟩ := ha
  obtain ⟨b, hb, hvb⟩ := hb
  have back : (b = w ∨ Descendant E b w) → (v = w ∨ Descendant E v w) := by
    rintro (rfl | hbw)
    · exact Or.inr hvb
    · exact Or.inr (hvb.trans hbw)
  rcases ha with ha | ⟨⟨a0, ha0, ha0a⟩, _⟩
  · rcases hb with hb | ⟨_, hbw⟩
    · exact Or.inl (hS v ⟨a, ha, hav⟩ ⟨b, hb, hvb⟩)
    · exact Or.inr ⟨⟨a, ha, hav⟩, back hbw⟩
  · rcases hb with hb | ⟨_, hbw⟩
    · exact Or.inl (hS v ⟨a0, ha0, ha0a.trans hav⟩ ⟨b, hb, hvb⟩)
    · exact Or.inr ⟨⟨a0, ha0, ha0a.trans hav⟩, back hbw⟩

theorem extension_added_finite (E : Graph) (S : NatSet) (w : Nat)
    (horder : ∀ u v, E u v → u < v) :
    FiniteSupport (fun v => Extension E S w v ∧ ¬ S v) := by
  apply (finiteSupport_iff_bounded _).mpr
  refine ⟨w + 1, ?_⟩
  intro v hv
  rcases hv.1 with hs | ⟨_, rfl | hd⟩
  · exact False.elim (hv.2 hs)
  · omega
  · have := descendant_strict horder hd
    omega

theorem extension_iap (E : Graph) (S : NatSet) (w : Nat)
    (horder : ∀ u v, E u v → u < v) (hiap : IAP E S) (hconv : Convex E S) :
    IAP E (Extension E S w) := by
  classical
  have hf := extension_added_finite E S w horder
  intro v hv
  by_cases hsv : S v
  · rcases hiap v hsv with hd | hn
    · apply Or.inl
      apply finiteSupport_mono (T := fun z => (S z ∧ Descendant E v z) ∨
        (Extension E S w z ∧ ¬ S z)) _ (finiteSupport_union hd hf)
      intro z hz
      by_cases hs : S z
      · exact Or.inl ⟨hs, hz.2⟩
      · exact Or.inr ⟨hz.1, hs⟩
    · apply Or.inr
      apply finiteSupport_mono (T := fun z => (S z ∧ ¬ Descendant E v z) ∨
        (Extension E S w z ∧ ¬ S z)) _ (finiteSupport_union hn hf)
      intro z hz
      by_cases hs : S z
      · exact Or.inl ⟨hs, hz.2⟩
      · exact Or.inr ⟨hz.1, hs⟩
  · apply Or.inl
    apply finiteSupport_mono (T := fun z => Extension E S w z ∧ ¬ S z) _ hf
    intro z hz
    refine ⟨hz.1, ?_⟩
    intro hsz
    rcases hv with hs | ⟨hanc, _⟩
    · exact hsv hs
    · exact hsv (hconv v hanc ⟨z, hsz, hz.2⟩)

theorem extension_connected (E : Graph) (S : NatSet) (w : Nat)
    (hconn : WeaklyConnected E S) (hconv : Convex E S) :
    WeaklyConnected E (Extension E S w) := by
  have hsub : ∀ v, S v → Extension E S w v := fun _ h => Or.inl h
  have hconv' := extension_convex E S w hconv
  have attach : ∀ v, Extension E S w v →
      ∃ a, S a ∧ WeakReach E (Extension E S w) a v := by
    intro v hv
    rcases hv with hs | ⟨⟨a, ha, hav⟩, hlast⟩
    · exact ⟨v, hs, .refl (Or.inl hs)⟩
    · exact ⟨a, ha, descendant_weakReach_convex hconv' hav (Or.inl ha)
        (Or.inr ⟨⟨a, ha, hav⟩, hlast⟩)⟩
  refine ⟨hconn.1.imp (fun _ h => Or.inl h), ?_⟩
  intro u v hu hv
  obtain ⟨a, ha, hau⟩ := attach u hu
  obtain ⟨b, hb, hbv⟩ := attach v hv
  exact .trans hau.symm (.trans (weakReach_mono_set hsub (hconn.2 a b ha hb)) hbv)

/-- A maximal specieslike cluster cannot omit any descendant. The finite
past hypothesis is supplied by strict identity natural birth order. -/
theorem maximal_specieslike_descendantClosed (E : Graph) (S : NatSet)
    (horder : ∀ u v, E u v → u < v) (hmax : MaximalSpecieslike E S) :
    DescendantClosed E S := by
  intro u w hu huw
  have hs : Specieslike E (Extension E S w) :=
    ⟨extension_connected E S w hmax.1.1 hmax.1.2.2,
      extension_iap E S w horder hmax.1.2.1 hmax.1.2.2,
      extension_convex E S w hmax.1.2.2⟩
  exact hmax.2 _ (fun _ h => Or.inl h) hs w (Or.inr ⟨⟨u, hu, huw⟩, Or.inl rfl⟩)

theorem descendant_induced_of_descendantClosed {E : Graph} {S : NatSet}
    (hclosed : DescendantClosed E S) {u v : Nat} (h : Descendant E u v)
    (hu : S u) : Descendant (Induced E S) u v := by
  induction h with
  | edge he => exact .edge ⟨hu, hclosed _ _ hu (.edge he), he⟩
  | snoc hd he ih =>
    have hm := hclosed _ _ hu hd
    exact .snoc ih ⟨hm, hclosed _ _ hm (.edge he), he⟩

def RelativeCore (E : Graph) (S : NatSet) : NatSet := fun v => S v ∧ Core (Induced E S) v

theorem descendant_induced_of_convex {E : Graph} {S : NatSet}
    (hconv : Convex E S) {u v : Nat} (h : Descendant E u v) (hu : S u) (hv : S v) :
    Descendant (Induced E S) u v := by
  induction h with
  | edge he => exact .edge ⟨hu, hv, he⟩
  | snoc hd he ih =>
    have hm := hconv _ ⟨u, hu, hd⟩ ⟨_, hv, .edge he⟩
    exact .snoc (ih hm) ⟨hm, hv, he⟩

/-- CA/REF-constrained maxima are covered through their actual Convex and
Reflection axioms; descendant closure is not asserted for those maxima. -/
theorem relativeCore_eq_inter_of_convex_reflection (E : Graph) (S : NatSet)
    (hconv : Convex E S) (href : Reflection E S) :
    RelativeCore E S = fun v => S v ∧ Core E v := by
  funext v
  apply propext
  constructor
  · rintro ⟨hv, hp⟩
    exact ⟨hv, infiniteSupport_mono (fun _ h => descendant_mono (fun _ _ he => he.2.2) h) hp⟩
  · rintro ⟨hv, hp⟩
    exact ⟨hv, infiniteSupport_mono
      (fun _ h => descendant_induced_of_convex hconv h.2 hv h.1) (href v hv hp)⟩

theorem four_axioms_pruning_commutes (E : Graph) (S : NatSet)
    (h : SpeciesRootCriterion.FourAxioms E S) :
    RelativeCore E S = fun v => S v ∧ Core E v :=
  relativeCore_eq_inter_of_convex_reflection E S h.2.1 h.2.2.2

theorem relativeCore_eq_inter_of_descendantClosed (E : Graph) (S : NatSet)
    (hclosed : DescendantClosed E S) :
    RelativeCore E S = fun v => S v ∧ Core E v := by
  funext v
  apply propext
  constructor
  · rintro ⟨hv, hp⟩
    exact ⟨hv, infiniteSupport_mono (fun _ h => descendant_mono (fun _ _ he => he.2.2) h) hp⟩
  · rintro ⟨hv, hp⟩
    exact ⟨hv, infiniteSupport_mono (fun _ h => descendant_induced_of_descendantClosed hclosed h hv) hp⟩

theorem maximal_cluster_pruning_commutes (E : Graph) (S : NatSet)
    (horder : ∀ u v, E u v → u < v) (hmax : MaximalSpecieslike E S) :
    RelativeCore E S = fun v => S v ∧ Core E v :=
  relativeCore_eq_inter_of_descendantClosed E S (maximal_specieslike_descendantClosed E S horder hmax)

theorem maximal_specieslike_reflection (E : Graph) (S : NatSet)
    (horder : ∀ u v, E u v → u < v) (hmax : MaximalSpecieslike E S) : Reflection E S := by
  intro v hv hp
  exact infiniteSupport_mono (fun w h =>
    ⟨maximal_specieslike_descendantClosed E S horder hmax v w hv h, h⟩) hp

/-- A nonmaximal cluster can lose all productivity on restriction, even in
the actual source population geometry. -/
theorem nonmaximal_cluster_productivity_counterexample :
    Specieslike PsEdge (fun v => v = 0) ∧ Core PsEdge 0 ∧
      ¬ RelativeCore PsEdge (fun v => v = 0) 0 := by
  refine ⟨⟨⟨⟨0, rfl⟩, ?_⟩, psSubset_iap _, ?_⟩, psDescendants_infinite 0, ?_⟩
  · intro u v hu hv
    subst u
    subst v
    exact .refl rfl
  · intro v _ hf
    obtain ⟨d, rfl, h⟩ := hf
    exact False.elim (no_psDescendant_zero v h)
  · intro hp
    apply hp.2
    refine ⟨[], ?_⟩
    intro w hw
    have noedge : ∀ u v, ¬ Induced PsEdge (fun v => v = 0) u v := by
      intro u v he
      have := he.2.2.1
      have := he.2.1
      omega
    cases hw with
    | edge he => exact False.elim (noedge _ _ he)
    | snoc _ he => exact False.elim (noedge _ _ he)

/-- The two-ray shared-root geometry of Alexander's constrained-cluster
example: zero branches to one and two; each positive ray advances by two. -/
def ForkEdge (u v : Nat) : Prop := v = u + 2 ∨ (u = 0 ∧ v = 1)

def OddRay (v : Nat) : Prop := v = 0 ∨ v % 2 = 1

theorem fork_strict (u v : Nat) (h : ForkEdge u v) : u < v := by
  unfold ForkEdge at h
  omega

theorem fork_descendant_iff (u v : Nat) :
    Descendant ForkEdge u v ↔ u < v ∧ (u = 0 ∨ u % 2 = v % 2) := by
  constructor
  · intro h
    refine ⟨descendant_strict fork_strict h, ?_⟩
    induction h with
    | edge he => unfold ForkEdge at he; omega
    | snoc hd he ih =>
      have hm := descendant_strict fork_strict hd
      unfold ForkEdge at he
      omega
  · intro h
    induction v using Nat.strongRecOn with
    | ind v ih =>
      by_cases h1 : v = 1
      · exact .edge (Or.inr (by omega))
      · by_cases h2 : v = u + 2
        · exact .edge (Or.inl h2)
        · have hmid : u < v - 2 ∧ (u = 0 ∨ u % 2 = (v - 2) % 2) := by omega
          exact .snoc (ih (v - 2) (by omega) hmid) (Or.inl (by omega))

theorem fork_naturalDateBiosphere : NaturalDateBiosphere ForkEdge := by
  refine ⟨fork_strict, finite_birthdate_prefix, ?_, whole_infinite⟩
  intro u
  refine ⟨[u + 2, 1], ?_⟩
  intro v hv
  rcases hv with h | h
  · simp [h]
  · simp [h.2]

theorem fork_descendants_infinite (v : Nat) : InfiniteSupport (Descendant ForkEdge v) := by
  intro hf
  obtain ⟨b, hb⟩ := (finiteSupport_iff_bounded _).mp hf
  have hd : Descendant ForkEdge v (v + 2 * (b + 1)) :=
    (fork_descendant_iff _ _).mpr (by omega)
  have := hb _ hd
  omega

theorem oddRay_internal_descendants_infinite (v : Nat) (hv : OddRay v) :
    InfiniteSupport (fun w => OddRay w ∧ Descendant ForkEdge v w) := by
  intro hf
  obtain ⟨b, hb⟩ := (finiteSupport_iff_bounded _).mp hf
  let w := 2 * (b + v + 1) + 1
  have hw : OddRay w := Or.inr (by dsimp [w]; omega)
  have hd : Descendant ForkEdge v w := (fork_descendant_iff _ _).mpr (by
    unfold OddRay at hv
    dsimp [w]
    omega)
  have := hb w ⟨hw, hd⟩
  dsimp [w] at this
  omega

theorem oddRay_iap : IAP ForkEdge OddRay := by
  intro v hv
  apply Or.inr
  apply (finiteSupport_iff_bounded _).mpr
  refine ⟨v + 1, ?_⟩
  rintro w ⟨hw, hn⟩
  have : ¬ (v < w ∧ (v = 0 ∨ v % 2 = w % 2)) :=
    fun h => hn ((fork_descendant_iff _ _).mpr h)
  unfold OddRay at hv hw
  omega

theorem oddRay_convex : Convex ForkEdge OddRay := by
  intro v _ hf
  obtain ⟨w, hw, hd⟩ := hf
  have h := (fork_descendant_iff _ _).mp hd
  unfold OddRay at hw ⊢
  omega

theorem oddRay_commonAncestor : CommonAncestor ForkEdge OddRay := by
  refine ⟨0, Or.inl rfl, ?_⟩
  intro w _ hne
  exact (fork_descendant_iff _ _).mpr ⟨by omega, Or.inl rfl⟩

theorem oddRay_reflection : Reflection ForkEdge OddRay :=
  fun v hv _ => oddRay_internal_descendants_infinite v hv

theorem oddRay_specieslike : Specieslike ForkEdge OddRay := by
  refine ⟨⟨⟨0, Or.inl rfl⟩, ?_⟩, oddRay_iap, oddRay_convex⟩
  have fromRoot : ∀ v, OddRay v → WeakReach ForkEdge OddRay 0 v := by
    intro v hv
    by_cases heq : v = 0
    · subst v
      exact .refl (Or.inl rfl)
    · exact descendant_weakReach_convex oddRay_convex
        ((fork_descendant_iff _ _).mpr ⟨by omega, Or.inl rfl⟩) (Or.inl rfl) hv
  intro u v hu hv
  exact .trans (fromRoot u hu).symm (fromRoot v hv)

theorem oddRay_maximalFourAxioms : SpeciesRootCriterion.MaximalFourAxioms ForkEdge OddRay := by
  classical
  refine ⟨⟨oddRay_iap, oddRay_convex, oddRay_commonAncestor, oddRay_reflection⟩, ?_⟩
  intro T hsub hT v hv
  by_cases hs : OddRay v
  · exact hs
  · apply False.elim
    have h1 : T 1 := hsub 1 (Or.inr rfl)
    rcases hT.1 1 h1 with hd | hn
    · exact oddRay_internal_descendants_infinite 1 (Or.inr rfl)
        (finiteSupport_mono (fun w hw => ⟨hsub w hw.1, hw.2⟩) hd)
    · have hp := hT.2.2.2 v hv (fork_descendants_infinite v)
      apply hp
      apply finiteSupport_mono (T := fun w => T w ∧ ¬ Descendant ForkEdge 1 w) _ hn
      intro w hw
      refine ⟨hw.1, ?_⟩
      intro h1w
      have h := (fork_descendant_iff _ _).mp hw.2
      have h' := (fork_descendant_iff _ _).mp h1w
      unfold OddRay at hs
      omega

/-- Constrained maximality does not imply descendant closure: REF prevents
adjoining only a finite initial piece of the other infinite ray. -/
theorem constrained_maximum_not_descendantClosed :
    NaturalDateBiosphere ForkEdge ∧
    SpeciesRootCriterion.MaximalFourAxioms ForkEdge OddRay ∧
    Specieslike ForkEdge OddRay ∧ ¬ DescendantClosed ForkEdge OddRay := by
  refine ⟨fork_naturalDateBiosphere, oddRay_maximalFourAxioms, oddRay_specieslike, ?_⟩
  intro hclosed
  have h := hclosed 0 2 (Or.inl rfl) (.edge (Or.inl rfl))
  unfold OddRay at h
  omega

end ProductiveCore

#print axioms ProductiveCore.core_infinite
#print axioms ProductiveCore.core_population
#print axioms ProductiveCore.reindexed_core_whole_inspecies
#print axioms ProductiveCore.reindexed_core_whole_specieslike
#print axioms ProductiveCore.reindexed_core_language_iff
#print axioms ProductiveCore.productive_core_theorem
#print axioms ProductiveCore.maximal_specieslike_descendantClosed
#print axioms ProductiveCore.maximal_cluster_pruning_commutes
#print axioms ProductiveCore.four_axioms_pruning_commutes
#print axioms ProductiveCore.nonmaximal_cluster_productivity_counterexample
#print axioms ProductiveCore.constrained_maximum_not_descendantClosed
