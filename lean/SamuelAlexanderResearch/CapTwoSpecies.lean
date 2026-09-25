import SamuelAlexanderResearch.CapTwo

/-! The optimal two-child line-graph avoider is itself an inspecies. -/

namespace CapTwoSpecies
open SpeciesBridge FixedGenderLift CapTwo

theorem reaches_later_source (x : Nat) (hx : Vertices x) (u : Nat)
    (hu : target x ≤ u) :
    ∀ y, Vertices y → source y = u → Descendant Arc x y := by
  have htarget := target_lower x hx
  induction u with
  | zero => omega
  | succ u ih =>
    intro y hy hsource
    by_cases he : target x = u+1
    · exact .edge ⟨hx, hy, hsource.trans he.symm⟩
    · have hu' : target x ≤ u := by omega
      have hz : Vertices (2*u) := by dsimp [Vertices]; omega
      have hs : source (2*u) = u := by dsimp [source]; omega
      have ht : target (2*u) = u+1 := by dsimp [target, source]; omega
      exact .snoc (ih hu' (2*u) hz hs) ⟨hz, hy, hsource.trans ht.symm⟩

theorem descendant_members {x y : Nat} (h : Descendant Arc x y) :
    Vertices x ∧ Vertices y := by
  induction h with
  | edge h => exact ⟨h.1, h.2.1⟩
  | snoc _ h ih => exact ⟨ih.1, h.2.1⟩

theorem nonDescendants_bounded (x : Nat) (hx : Vertices x) (y : Nat)
    (hn : ¬Descendant Arc x y) : y < 2*target x := by
  have ht := target_lower x hx
  by_cases hy : 2*target x ≤ y
  · have hyv : Vertices y := by dsimp [Vertices]; omega
    have hys : target x ≤ source y := by dsimp [source]; omega
    exact False.elim (hn (reaches_later_source x hx (source y) hys y hyv rfl))
  · omega

theorem vertices_ancestrallyClosed : AncestrallyClosed Arc Vertices := by
  intro x y _ h
  exact (descendant_members h).1

theorem vertices_convex : Convex Arc Vertices := by
  intro v _ h
  obtain ⟨y, _, hvy⟩ := h
  exact (descendant_members hvy).1

theorem vertices_iap : IAP Arc Vertices := by
  intro x hx
  apply Or.inr
  exact (finiteSupport_iff_bounded _).mpr
    ⟨2*target x, fun y hy => nonDescendants_bounded x hx y hy.2⟩

theorem descendant_weakReach {x y : Nat} (h : Descendant Arc x y) :
    WeakReach Arc Vertices x y := by
  induction h with
  | edge h => exact .edge h.1 h.2.1 (Or.inl h)
  | snoc _ h ih => exact .trans ih (.edge h.1 h.2.1 (Or.inl h))

theorem vertices_connected : WeaklyConnected Arc Vertices := by
  refine ⟨⟨1, by change 1 ≤ 1; omega⟩, ?_⟩
  intro x y hx hy
  let z := 2*(target x+target y)
  have ht := target_lower x hx
  have hz : Vertices z := by dsimp [Vertices, z]; omega
  have hs : source z = target x+target y := by dsimp [source, z]; omega
  have hxy := reaches_later_source x hx (target x+target y) (by omega) z hz hs
  have hyz := reaches_later_source y hy (target x+target y) (by omega) z hz hs
  exact .trans (descendant_weakReach hxy) (descendant_weakReach hyz).symm

theorem vertices_specieslike : Specieslike Arc Vertices :=
  ⟨vertices_connected, vertices_iap, vertices_convex⟩

theorem vertices_inspecies : Inspecies Arc Vertices := by
  refine ⟨vertices_infinite, vertices_ancestrallyClosed, ?_⟩
  intro T _ hinf hclosed x hx
  classical
  by_cases h : T x
  · exact h
  · apply False.elim
    apply hinf
    apply (finiteSupport_iff_bounded _).mpr
    refine ⟨2*target x, ?_⟩
    intro y hy
    apply nonDescendants_bounded x hx y
    intro hd
    exact h (hclosed x y hy hd)

theorem vertices_reflection : Reflection Arc Vertices := by
  intro x _ hinf hfinite
  apply hinf
  exact finiteSupport_mono (fun _ h => ⟨(descendant_members h).2, h⟩) hfinite

theorem induced_eq : Induced Arc Vertices = Arc := by
  funext x y
  apply propext
  constructor
  · intro h; exact h.2.2
  · intro h; exact ⟨h.1, h.2.1, h⟩

/-- The optimal-cap witness has all species properties in its actual induced graph. -/
theorem cap_two_inspecies_avoider (s : Nat → Bool)
    (hs : ¬BinaryAvoidance.EventuallyPeriodic s) :
    FixedGenderPopulation Arc Vertices (CapTwo.gender s) 2 ∧
    Specieslike (Induced Arc Vertices) Vertices ∧
    Inspecies (Induced Arc Vertices) Vertices ∧
    Reflection (Induced Arc Vertices) Vertices ∧
    ¬FixedGenderReindex.RealizesOn Arc Vertices (CapTwo.gender s) s := by
  rw [induced_eq]
  exact ⟨fixedGenderPopulation s, vertices_specieslike, vertices_inspecies,
    vertices_reflection, avoids_aperiodic s hs⟩

#print axioms reaches_later_source
#print axioms vertices_inspecies
#print axioms cap_two_inspecies_avoider

end CapTwoSpecies
