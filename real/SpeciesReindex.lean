import RealFounderWindow

/-!
# Faithful species-predicate transport by an ordered enumeration

Only organisms are relabelled. Their literal real birth dates and the fixed
real founding duration are preserved. Equal birth dates are allowed. The
transport equivalences use the bijection, while strict order of the indexed
edges follows separately from the chronological property of the original graph.
-/

namespace SpeciesReindex
open SpeciesBridge FounderWindowResearch BirthOrder

noncomputable section
variable {birth : Nat → ℝ}

def pullGraph (e : OrderedEnumeration birth) (E : Graph) : Graph :=
  fun i j => E (e.toFun i) (e.toFun j)

def pullSet (e : OrderedEnumeration birth) (S : NatSet) : NatSet :=
  fun i => S (e.toFun i)

def pushSet (e : OrderedEnumeration birth) (T : NatSet) : NatSet :=
  fun v => T (e.index v)

def pulledBirth (e : OrderedEnumeration birth) : Nat → ℝ := fun i => birth (e.toFun i)

variable (e : OrderedEnumeration birth)

theorem pull_push (T : NatSet) : pullSet e (pushSet e T) = T := by
  funext i
  exact congrArg T (e.index_toFun i)

theorem push_pull (S : NatSet) : pushSet e (pullSet e S) = S := by
  funext v
  exact congrArg S (e.toFun_index v)

theorem inclusion_iff (S T : NatSet) :
    (∀ i, pullSet e S i → pullSet e T i) ↔ (∀ v, S v → T v) := by
  constructor
  · intro h v hv
    obtain ⟨i, rfl⟩ := e.surjective v
    exact h i hv
  · intro h i hi
    exact h _ hi

theorem pull_union {I : Type} (C : I → NatSet) :
    pullSet e (Union C) = Union (fun i => pullSet e (C i)) := rfl

theorem directed_iff {I : Type} (C : I → NatSet) :
    Directed (fun i => pullSet e (C i)) ↔ Directed C := by
  constructor
  · intro h i j
    obtain ⟨k, hik, hjk⟩ := h i j
    exact ⟨k, (inclusion_iff e _ _).mp hik, (inclusion_iff e _ _).mp hjk⟩
  · intro h i j
    obtain ⟨k, hik, hjk⟩ := h i j
    exact ⟨k, (inclusion_iff e _ _).mpr hik, (inclusion_iff e _ _).mpr hjk⟩

theorem descendant_map {E : Graph} {i j : Nat} (h : Descendant (pullGraph e E) i j) :
    Descendant E (e.toFun i) (e.toFun j) := by
  induction h with
  | edge he => exact .edge he
  | snoc _ he ih => exact .snoc ih he

theorem descendant_index {E : Graph} {a b : Nat} (h : Descendant E a b) :
    Descendant (pullGraph e E) (e.index a) (e.index b) := by
  induction h with
  | edge he =>
    exact .edge (by simpa only [pullGraph, e.toFun_index] using he)
  | snoc _ he ih =>
    exact .snoc ih (by simpa only [pullGraph, e.toFun_index] using he)

theorem descendant_iff (E : Graph) (i j : Nat) :
    Descendant (pullGraph e E) i j ↔ Descendant E (e.toFun i) (e.toFun j) := by
  constructor
  · exact descendant_map e
  · intro h
    simpa only [e.index_toFun] using descendant_index e h

theorem finiteSupport_iff (S : NatSet) :
    FiniteSupport (pullSet e S) ↔ FiniteSupport S :=
  e.finiteCover_pullback_iff S

theorem infiniteSupport_iff (S : NatSet) :
    InfiniteSupport (pullSet e S) ↔ InfiniteSupport S :=
  not_congr (finiteSupport_iff e S)

private theorem finiteSupport_congr {S T : NatSet} (h : ∀ v, S v ↔ T v) :
    FiniteSupport S ↔ FiniteSupport T :=
  ⟨fun hs => finiteSupport_mono (fun v hv => (h v).mpr hv) hs,
   fun ht => finiteSupport_mono (fun v hv => (h v).mp hv) ht⟩

theorem finite_descendants_iff (E : Graph) (S : NatSet) (i : Nat) :
    FiniteSupport (fun j => pullSet e S j ∧ Descendant (pullGraph e E) i j) ↔
      FiniteSupport (fun v => S v ∧ Descendant E (e.toFun i) v) :=
  (finiteSupport_congr (fun j => and_congr Iff.rfl (descendant_iff e E i j))).trans
    (finiteSupport_iff e (fun v => S v ∧ Descendant E (e.toFun i) v))

theorem finite_nondescendants_iff (E : Graph) (S : NatSet) (i : Nat) :
    FiniteSupport (fun j => pullSet e S j ∧ ¬ Descendant (pullGraph e E) i j) ↔
      FiniteSupport (fun v => S v ∧ ¬ Descendant E (e.toFun i) v) :=
  (finiteSupport_congr (fun j => and_congr Iff.rfl (not_congr (descendant_iff e E i j)))).trans
    (finiteSupport_iff e (fun v => S v ∧ ¬ Descendant E (e.toFun i) v))

theorem infinite_descendants_iff (E : Graph) (i : Nat) :
    InfiniteSupport (Descendant (pullGraph e E) i) ↔
      InfiniteSupport (Descendant E (e.toFun i)) :=
  not_congr ((finiteSupport_congr (fun j => descendant_iff e E i j)).trans
    (finiteSupport_iff e (Descendant E (e.toFun i))))

theorem iap_iff (E : Graph) (S : NatSet) :
    IAP (pullGraph e E) (pullSet e S) ↔ IAP E S := by
  constructor
  · intro h v hv
    obtain ⟨i, rfl⟩ := e.surjective v
    rcases h i hv with hpos | hneg
    · exact Or.inl ((finite_descendants_iff e E S i).mp hpos)
    · exact Or.inr ((finite_nondescendants_iff e E S i).mp hneg)
  · intro h i hi
    rcases h (e.toFun i) hi with hpos | hneg
    · exact Or.inl ((finite_descendants_iff e E S i).mpr hpos)
    · exact Or.inr ((finite_nondescendants_iff e E S i).mpr hneg)

theorem convex_iff (E : Graph) (S : NatSet) :
    Convex (pullGraph e E) (pullSet e S) ↔ Convex E S := by
  constructor
  · intro h v ha hd
    obtain ⟨a, ha, hav⟩ := ha
    obtain ⟨d, hd, hvd⟩ := hd
    have hm := h (e.index v)
      ⟨e.index a, by simpa only [pullSet, e.toFun_index] using ha, descendant_index e hav⟩
      ⟨e.index d, by simpa only [pullSet, e.toFun_index] using hd, descendant_index e hvd⟩
    simpa only [pullSet, e.toFun_index] using hm
  · intro h i ha hd
    obtain ⟨a, ha, hai⟩ := ha
    obtain ⟨d, hd, hid⟩ := hd
    exact h (e.toFun i) ⟨e.toFun a, ha, descendant_map e hai⟩
      ⟨e.toFun d, hd, descendant_map e hid⟩

theorem reflection_iff (E : Graph) (S : NatSet) :
    Reflection (pullGraph e E) (pullSet e S) ↔ Reflection E S := by
  constructor
  · intro h v hv hinf
    obtain ⟨i, rfl⟩ := e.surjective v
    have hi := h i hv ((infinite_descendants_iff e E i).mpr hinf)
    exact (not_congr (finite_descendants_iff e E S i)).mp hi
  · intro h i hi hinf
    have hv := h (e.toFun i) hi ((infinite_descendants_iff e E i).mp hinf)
    exact (not_congr (finite_descendants_iff e E S i)).mpr hv

theorem weakReach_map {E : Graph} {S : NatSet} {i j : Nat}
    (h : WeakReach (pullGraph e E) (pullSet e S) i j) :
    WeakReach E S (e.toFun i) (e.toFun j) := by
  induction h with
  | refl hi => exact .refl hi
  | edge hi hj he => exact .edge hi hj he
  | trans _ _ ih ij => exact .trans ih ij

theorem weakReach_index {E : Graph} {S : NatSet} {a b : Nat}
    (h : WeakReach E S a b) :
    WeakReach (pullGraph e E) (pullSet e S) (e.index a) (e.index b) := by
  induction h with
  | refl ha => exact .refl (by simpa only [pullSet, e.toFun_index] using ha)
  | edge ha hb he =>
    exact .edge (by simpa only [pullSet, e.toFun_index] using ha)
      (by simpa only [pullSet, e.toFun_index] using hb)
      (by simpa only [pullGraph, e.toFun_index] using he)
  | trans _ _ ih ij => exact .trans ih ij

theorem weakReach_iff (E : Graph) (S : NatSet) (i j : Nat) :
    WeakReach (pullGraph e E) (pullSet e S) i j ↔
      WeakReach E S (e.toFun i) (e.toFun j) := by
  constructor
  · exact weakReach_map e
  · intro h
    simpa only [e.index_toFun] using weakReach_index e h

theorem weaklyConnected_iff (E : Graph) (S : NatSet) :
    WeaklyConnected (pullGraph e E) (pullSet e S) ↔ WeaklyConnected E S := by
  constructor
  · rintro ⟨⟨i, hi⟩, paths⟩
    refine ⟨⟨e.toFun i, hi⟩, ?_⟩
    intro a b ha hb
    obtain ⟨i, rfl⟩ := e.surjective a
    obtain ⟨j, rfl⟩ := e.surjective b
    exact weakReach_map e (paths i j ha hb)
  · rintro ⟨⟨a, ha⟩, paths⟩
    obtain ⟨i, rfl⟩ := e.surjective a
    refine ⟨⟨i, ha⟩, ?_⟩
    intro j k hj hk
    exact (weakReach_iff e E S j k).mpr (paths _ _ hj hk)

theorem commonAncestor_iff (E : Graph) (S : NatSet) :
    CommonAncestor (pullGraph e E) (pullSet e S) ↔ CommonAncestor E S := by
  constructor
  · rintro ⟨i, hi, paths⟩
    refine ⟨e.toFun i, hi, ?_⟩
    intro v hv hne
    obtain ⟨j, rfl⟩ := e.surjective v
    exact (descendant_iff e E i j).mp
      (paths j hv (fun heq => hne (congrArg e.toFun heq)))
  · rintro ⟨a, ha, paths⟩
    obtain ⟨i, rfl⟩ := e.surjective a
    refine ⟨i, ha, ?_⟩
    intro j hj hne
    exact (descendant_iff e E i j).mpr
      (paths _ hj (fun heq => hne (e.injective j i heq)))

theorem founder_iff (E : Graph) (S : NatSet) (i : Nat) :
    Founder (pullGraph e E) (pullSet e S) i ↔ Founder E S (e.toFun i) := by
  constructor
  · rintro ⟨hi, noAncestor⟩
    refine ⟨hi, ?_⟩
    intro a ha hai
    obtain ⟨j, rfl⟩ := e.surjective a
    exact noAncestor j ha ((descendant_iff e E j i).mpr hai)
  · rintro ⟨hi, noAncestor⟩
    exact ⟨hi, fun j hj hji => noAncestor _ hj ((descendant_iff e E j i).mp hji)⟩

theorem finite_founders_iff (E : Graph) (S : NatSet) :
    FiniteSupport (Founder (pullGraph e E) (pullSet e S)) ↔
      FiniteSupport (Founder E S) :=
  (finiteSupport_congr (fun i => founder_iff e E S i)).trans
    (finiteSupport_iff e (Founder E S))

/-- The identical real duration is preserved; birth times are composed with the bijection. -/
theorem window_iff (E : Graph) (S : NatSet) (duration : ℝ) :
    RealFounderWindow.Window (pullGraph e E) (pulledBirth e) duration (pullSet e S) ↔
      RealFounderWindow.Window E birth duration S := by
  constructor
  · rintro ⟨i, hi, earliest, bound⟩
    refine ⟨e.toFun i, hi, ?_, ?_⟩
    · intro v hv
      obtain ⟨j, rfl⟩ := e.surjective v
      exact earliest j hv
    · intro r hr
      obtain ⟨j, rfl⟩ := e.surjective r
      exact bound j ((founder_iff e E S j).mpr hr)
  · rintro ⟨a, ha, earliest, bound⟩
    obtain ⟨i, rfl⟩ := e.surjective a
    refine ⟨i, ha, ?_, ?_⟩
    · intro j hj
      exact earliest _ hj
    · intro j hj
      exact bound _ ((founder_iff e E S j).mp hj)

theorem specieslike_iff (E : Graph) (S : NatSet) :
    Specieslike (pullGraph e E) (pullSet e S) ↔ Specieslike E S :=
  and_congr (weaklyConnected_iff e E S)
    (and_congr (iap_iff e E S) (convex_iff e E S))

theorem pulled_strict_sublevels (finite : RealFounderWindow.StrictFiniteSublevels birth) :
    RealFounderWindow.StrictFiniteSublevels (pulledBirth e) := by
  intro t
  exact (finiteSupport_iff e (fun v => birth v < t)).mpr (finite t)

theorem pulled_chronological (E : Graph) (h : RealFounderWindow.Chronological E birth) :
    RealFounderWindow.Chronological (pullGraph e E) (pulledBirth e) :=
  fun i j he => h _ _ he

theorem pullGraph_strict (E : Graph) (h : RealFounderWindow.Chronological E birth) :
    ∀ i j, pullGraph e E i j → i < j :=
  e.edges_increase E h

theorem pulled_finite_children (E : Graph) (finite : ∀ v, FiniteSupport (E v)) :
    ∀ i, FiniteSupport (pullGraph e E i) := by
  intro i
  exact (finiteSupport_iff e (E (e.toFun i))).mpr (finite _)

/-- The enumeration is derived from the given real birth function and finite sublevels.
The actual vertex type Nat is infinite; neither an enumeration nor date injectivity is input. -/
def actualEnumeration (birth : Nat → ℝ)
    (finite : RealFounderWindow.StrictFiniteSublevels birth) : OrderedEnumeration birth :=
  BirthOrder.orderedEnumeration birth
    ((BirthOrder.infiniteVertices_iff_not_finiteCover Nat).mpr SpeciesBridge.whole_infinite)
    (RealFounderWindow.closed_sublevels finite)

/-- Every chronological real-birthdate graph has the exact rank presentation needed
by the natural-order species theorem, with its real dates retained separately. -/
theorem actual_presentation (E : Graph) (birth : Nat → ℝ)
    (finite : RealFounderWindow.StrictFiniteSublevels birth)
    (chronological : RealFounderWindow.Chronological E birth)
    (children : ∀ v, FiniteSupport (E v)) :
    let e := actualEnumeration birth finite
    (∀ i j, pullGraph e E i j → i < j) ∧
    (∀ i, FiniteSupport (pullGraph e E i)) ∧
    RealFounderWindow.StrictFiniteSublevels (pulledBirth e) ∧
    RealFounderWindow.Chronological (pullGraph e E) (pulledBirth e) ∧
    (∀ S duration,
      RealFounderWindow.Window (pullGraph e E) (pulledBirth e) duration (pullSet e S) ↔
        RealFounderWindow.Window E birth duration S) := by
  let e := actualEnumeration birth finite
  exact ⟨pullGraph_strict e E chronological, pulled_finite_children e E children,
    pulled_strict_sublevels e finite, pulled_chronological e E chronological,
    fun S duration => window_iff e E S duration⟩

end
end SpeciesReindex

#print axioms SpeciesReindex.descendant_iff
#print axioms SpeciesReindex.finiteSupport_iff
#print axioms SpeciesReindex.infiniteSupport_iff
#print axioms SpeciesReindex.iap_iff
#print axioms SpeciesReindex.convex_iff
#print axioms SpeciesReindex.reflection_iff
#print axioms SpeciesReindex.weakReach_iff
#print axioms SpeciesReindex.weaklyConnected_iff
#print axioms SpeciesReindex.commonAncestor_iff
#print axioms SpeciesReindex.founder_iff
#print axioms SpeciesReindex.finite_founders_iff
#print axioms SpeciesReindex.window_iff
#print axioms SpeciesReindex.specieslike_iff
#print axioms SpeciesReindex.actual_presentation
