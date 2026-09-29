import SamuelAlexanderResearch.ProductiveCore

/-! Reflection survives nonempty downward-directed intersections of convex
reflecting sets in the strict natural-date, finite-child model. -/
namespace SeedIntersections

open SpeciesBridge SpeciesGlobalIAP

def Inter {I : Type} (C : I → NatSet) : NatSet := fun v => ∀ i, C i v

def DownDirected {I : Type} (C : I → NatSet) : Prop :=
  ∀ i j, ∃ k, (∀ v, C k v → C i v) ∧ (∀ v, C k v → C j v)

theorem convex_intersection {E : Graph} {I : Type} {C : I → NatSet}
    (hconv : ∀ i, Convex E (C i)) : Convex E (Inter C) := by
  intro w ha hd i
  obtain ⟨a, ha, haw⟩ := ha
  obtain ⟨d, hd, hwd⟩ := hd
  exact hconv i w ⟨a, ha i, haw⟩ ⟨d, hd i, hwd⟩

/-- A finite set that meets every downward-directed stage has a member common
to all stages. No assumption of linear ordering of the stages is needed. -/
theorem finite_persistent_member {I : Type} [Nonempty I] {C : I → NatSet}
    (P : NatSet) (hP : FiniteSupport P) (hdir : DownDirected C)
    (hhit : ∀ i, ∃ w, P w ∧ C i w) : ∃ w, P w ∧ Inter C w := by
  classical
  apply Classical.byContradiction
  intro hn
  have homit : ∀ w, P w → ∃ i, ¬ C i w := by
    intro w hw
    apply Classical.byContradiction
    intro hnone
    apply hn
    refine ⟨w, hw, ?_⟩
    intro i
    exact Classical.byContradiction (fun hnot => hnone ⟨i, hnot⟩)
  have avoid : ∀ n, ∃ i, ∀ w, w < n → P w → ¬ C i w := by
    intro n
    induction n with
    | zero =>
      obtain ⟨i⟩ := ‹Nonempty I›
      exact ⟨i, fun w hw _ _ => Nat.not_lt_zero w hw⟩
    | succ n ih =>
      obtain ⟨i, hi⟩ := ih
      by_cases hp : P n
      · obtain ⟨j, hj⟩ := homit n hp
        obtain ⟨k, hki, hkj⟩ := hdir i j
        refine ⟨k, ?_⟩
        intro w hw hPw hCw
        by_cases hlt : w < n
        · exact hi w hlt hPw (hki w hCw)
        · have heq : w = n := by omega
          subst w
          exact hj (hkj n hCw)
      · refine ⟨i, ?_⟩
        intro w hw hPw hCw
        have hlt : w < n := by
          by_cases heq : w = n
          · exact False.elim (hp (heq ▸ hPw))
          · omega
        exact hi w hlt hPw hCw
  obtain ⟨N, hN⟩ := (finiteSupport_iff_bounded P).mp hP
  obtain ⟨i, hi⟩ := avoid N
  obtain ⟨w, hw, hiw⟩ := hhit i
  exact hi w (hN w hw) hw hiw

/-- A productive vertex common to all stages has an ambient-productive child
common to all stages. Each stage supplies a productive induced-graph child;
the finite persistent-member lemma synchronizes that choice. -/
theorem persistent_productive_child {E : Graph} {I : Type} [Nonempty I]
    {C : I → NatSet}
    (hchildren : ∀ a, FiniteSupport (E a))
    (hdir : DownDirected C)
    (hconv : ∀ i, Convex E (C i))
    (href : ∀ i, Reflection E (C i))
    (x : Nat) (hx : Inter C x) (hprod : ProductiveCore.Core E x) :
    ∃ y, E x y ∧ Inter C y ∧ ProductiveCore.Core E y := by
  let P : NatSet := fun y => E x y ∧ ProductiveCore.Core E y
  have hP : FiniteSupport P :=
    finiteSupport_mono (fun _ h => h.1) (hchildren x)
  have hhit : ∀ i, ∃ y, P y ∧ C i y := by
    intro i
    let F := ProductiveCore.Induced E (C i)
    have hFchildren : ∀ a, FiniteSupport (F a) :=
      fun a => finiteSupport_mono (fun _ he => he.2.2) (hchildren a)
    have hFprod : ProductiveCore.Core F x :=
      infiniteSupport_mono
        (fun _ h => ProductiveCore.descendant_induced_of_convex (hconv i) h.2 (hx i) h.1)
        (href i x (hx i) hprod)
    obtain ⟨y, hxy, hyprod⟩ := ProductiveCore.productive_child F hFchildren x hFprod
    have hyAmbient : ProductiveCore.Core E y :=
      infiniteSupport_mono
        (fun _ h => ProductiveCore.descendant_mono (fun _ _ he => he.2.2) h) hyprod
    exact ⟨y, ⟨hxy.2.2, hyAmbient⟩, hxy.2.1⟩
  obtain ⟨y, hy, hIy⟩ := finite_persistent_member P hP hdir hhit
  exact ⟨y, hy.1, hIy, hy.2⟩

/-- Full reflection, with global infinitude in its premise and infinitude
inside the actual intersection in its conclusion. -/
theorem reflection_intersection {E : Graph} {I : Type} [Nonempty I]
    {C : I → NatSet}
    (horder : ∀ a b, E a b → a < b)
    (hchildren : ∀ a, FiniteSupport (E a))
    (hdir : DownDirected C)
    (hconv : ∀ i, Convex E (C i))
    (href : ∀ i, Reflection E (C i)) : Reflection E (Inter C) := by
  intro x hx hprod
  have large : ∀ n, ∃ y, Inter C y ∧ ProductiveCore.Core E y ∧
      Descendant E x y ∧ n ≤ y := by
    intro n
    induction n with
    | zero =>
      obtain ⟨y, hxy, hy, hp⟩ :=
        persistent_productive_child hchildren hdir hconv href x hx hprod
      exact ⟨y, hy, hp, .edge hxy, Nat.zero_le _⟩
    | succ n ih =>
      obtain ⟨y, hy, hp, hxy, hn⟩ := ih
      obtain ⟨z, hyz, hz, hpz⟩ :=
        persistent_productive_child hchildren hdir hconv href y hy hp
      refine ⟨z, hz, hpz, .snoc hxy hyz, ?_⟩
      have hstrict := horder y z hyz
      omega
  intro hfinite
  obtain ⟨bound, hbound⟩ := (finiteSupport_iff_bounded _).mp hfinite
  obtain ⟨y, hy, _, hxy, hlarge⟩ := large bound
  have hsmall := hbound y ⟨hy, hxy⟩
  omega

end SeedIntersections

#print axioms SeedIntersections.convex_intersection
#print axioms SeedIntersections.finite_persistent_member
#print axioms SeedIntersections.persistent_productive_child
#print axioms SeedIntersections.reflection_intersection
