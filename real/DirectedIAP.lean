import FounderWindow
import SamuelAlexanderResearch.ProductiveCore

/-! Scratch proof of directed-union IAP closure with finite internal founders.
The graph, strict ancestry, convexity, IAP and reflection are the existing
SpeciesBridge definitions. No infinite-ray premise is assumed. -/
namespace DirectedIAPResearch

open SpeciesBridge SpeciesGlobalIAP FounderWindowResearch

abbrev Bad (E : Graph) (U : NatSet) (v : Nat) : NatSet :=
  fun w => U w ∧ ¬ Descendant E v w

theorem directed_union_convex {E : Graph} {I : Type} {C : I → NatSet}
    (hdir : Directed C) (hconv : ∀ i, Convex E (C i)) :
    Convex E (Union C) := by
  intro w ha hd
  obtain ⟨a, ⟨i, hi⟩, haw⟩ := ha
  obtain ⟨d, ⟨j, hj⟩, hwd⟩ := hd
  obtain ⟨k, hik, hjk⟩ := hdir i j
  exact ⟨k, hconv k w ⟨a, hik a hi, haw⟩ ⟨d, hjk d hj, hwd⟩⟩

theorem bad_convex {E : Graph} {U : NatSet} (hconv : Convex E U) (v : Nat) :
    Convex E (Bad E U v) := by
  intro w ha hd
  obtain ⟨a, ha, haw⟩ := ha
  obtain ⟨d, hd, hwd⟩ := hd
  exact ⟨hconv w ⟨a, ha.1, haw⟩ ⟨d, hd.1, hwd⟩,
    fun hvw => hd.2 (hvw.trans hwd)⟩

/-- A finite founder cover forces one founder to have infinitely many bad
vertices below it in the actual graph induced on the nondescendant region. -/
theorem bad_founder_productive {E : Graph} {U : NatSet} {v : Nat}
    (horder : ∀ a b, E a b → a < b)
    (hconv : Convex E U)
    (hfounders : FiniteSupport (Founder E U))
    (hbad : InfiniteSupport (Bad E U v)) :
    ∃ r, Founder E U r ∧ Bad E U v r ∧
      ProductiveCore.Core (ProductiveCore.Induced E (Bad E U v)) r := by
  classical
  let F := ProductiveCore.Induced E (Bad E U v)
  apply Classical.byContradiction
  intro hn
  have hfinite : ∀ r, Founder E U r → Bad E U v r →
      FiniteSupport (Descendant F r) := by
    intro r hr hBr
    exact Classical.byContradiction (fun hinf => hn ⟨r, hr, hBr, hinf⟩)
  obtain ⟨N, hN⟩ := (finiteSupport_iff_bounded _).mp hfounders
  obtain ⟨bound, hbound⟩ := PositiveUnavoidability.finite_union_bound
    (fun r w => Founder E U r ∧ Bad E U v r ∧ (w = r ∨ Descendant F r w)) N (by
      intro r _
      by_cases hr : Founder E U r ∧ Bad E U v r
      · exact (finiteSupport_iff_bounded _).mp
          (finiteSupport_mono (fun _ hw => hw.2.2)
            (ProductiveCore.finite_cone (hfinite r hr.1 hr.2)))
      · exact ⟨0, fun _ hw => False.elim (hr ⟨hw.1, hw.2.1⟩)⟩)
  apply hbad
  apply (finiteSupport_iff_bounded _).mpr
  refine ⟨bound, ?_⟩
  intro w hw
  obtain ⟨r, hr, hrw⟩ := founder_covers horder U w hw.1
  have hBr : Bad E U v r := by
    refine ⟨hr.1, ?_⟩
    intro hvr
    rcases hrw with heq | hrw
    · exact hw.2 (heq ▸ hvr)
    · exact hw.2 (hvr.trans hrw)
  have hcone : w = r ∨ Descendant F r w := by
    rcases hrw with heq | hrw
    · exact Or.inl heq.symm
    · exact Or.inr (ProductiveCore.descendant_induced_of_convex
        (bad_convex hconv v) hrw hBr hw)
  exact hbound r (hN r hr) w ⟨hr, hBr, hcone⟩

/-- The productive-child theorem gives arbitrarily large productive descendants
by finite induction, so an infinite-path choice principle is not needed. -/
theorem productive_descendants_unbounded (E : Graph)
    (horder : ∀ a b, E a b → a < b)
    (hchildren : ∀ a, FiniteSupport (E a))
    (r : Nat) (hr : ProductiveCore.Core E r) :
    ∀ n, ∃ w, (w = r ∨ Descendant E r w) ∧
      ProductiveCore.Core E w ∧ n ≤ w := by
  intro n
  induction n with
  | zero => exact ⟨r, Or.inl rfl, hr, Nat.zero_le _⟩
  | succ n ih =>
    obtain ⟨w, hcone, hw, hn⟩ := ih
    obtain ⟨z, hwz, hz⟩ := ProductiveCore.productive_child E hchildren w hw
    refine ⟨z, Or.inr ?_, hz, ?_⟩
    · rcases hcone with heq | hcone
      · subst w
        exact .edge hwz
      · exact .snoc hcone hwz
    · have hs := horder w z hwz
      omega

/-- Reflection and IAP in a common larger stage force a productive descendant
of a member back into a fixed infinite convex stage. -/
theorem capture_productive_descendant {E : Graph} {I : Type} {C : I → NatSet}
    (hdir : Directed C)
    (hconv : ∀ i, Convex E (C i))
    (hiap : ∀ i, IAP E (C i))
    (href : ∀ i, Reflection E (C i))
    (i : I) (r w : Nat) (hr : C i r)
    (hA : InfiniteSupport (C i)) (hw : Union C w)
    (hcone : w = r ∨ Descendant E r w)
    (hprod : InfiniteSupport (Descendant E w)) : C i w := by
  classical
  rcases hcone with heq | hrw
  · simpa [heq] using hr
  · obtain ⟨j, hj⟩ := hw
    obtain ⟨k, hik, hjk⟩ := hdir i j
    have hkw := hjk w hj
    have hdesc := href k w hkw hprod
    have hcofinite : FiniteSupport (fun z => C k z ∧ ¬ Descendant E w z) := by
      rcases hiap k w hkw with hfin | hfin
      · exact False.elim (hdesc hfin)
      · exact hfin
    have hz : ∃ z, C i z ∧ Descendant E w z := by
      apply Classical.byContradiction
      intro hn
      apply hA
      apply finiteSupport_mono (T := fun z => C k z ∧ ¬ Descendant E w z) _ hcofinite
      intro z hzi
      exact ⟨hik z hzi, fun hwz => hn ⟨z, hzi, hwz⟩⟩
    obtain ⟨z, hzi, hwz⟩ := hz
    exact hconv i w ⟨r, hr, hrw⟩ ⟨z, hzi, hwz⟩

/-- Directed unions of convex reflecting IAP sets retain IAP whenever the
union has finitely many internal ancestry-minimal members. -/
theorem iap_directed_union_of_finite_founders
    {E : Graph} {I : Type} [Nonempty I] {C : I → NatSet}
    (horder : ∀ u v, E u v → u < v)
    (hchildren : ∀ u, FiniteSupport (E u))
    (hdir : Directed C)
    (hconv : ∀ i, Convex E (C i))
    (hiap : ∀ i, IAP E (C i))
    (href : ∀ i, Reflection E (C i))
    (hfounders : FiniteSupport (Founder E (Union C))) : IAP E (Union C) := by
  classical
  intro v hv
  by_cases hd : FiniteSupport (fun w => Union C w ∧ Descendant E v w)
  · exact Or.inl hd
  · apply Or.inr
    apply Classical.byContradiction
    intro hbad
    let B := Bad E (Union C) v
    let F := ProductiveCore.Induced E B
    obtain ⟨r, hr, hBr, hrootprod⟩ := bad_founder_productive horder
      (directed_union_convex hdir hconv) hfounders hbad
    have hForder : ∀ a b, F a b → a < b :=
      fun a b he => horder a b he.2.2
    have hFchildren : ∀ a, FiniteSupport (F a) :=
      fun a => finiteSupport_mono (fun _ he => he.2.2) (hchildren a)
    have hFprod : ProductiveCore.Core F r := hrootprod
    have hrootAmbient : InfiniteSupport (Descendant E r) :=
      infiniteSupport_mono
        (fun _ h => ProductiveCore.descendant_mono (fun _ _ he => he.2.2) h) hFprod
    obtain ⟨iv, hiv⟩ := hv
    obtain ⟨ir, hir⟩ := hr.1
    obtain ⟨a, hva, hra⟩ := hdir iv ir
    have hav := hva v hiv
    have har := hra r hir
    have hA : InfiniteSupport (C a) :=
      infiniteSupport_mono (fun _ h => h.1) (href a r har hrootAmbient)
    have hvAmbient : InfiniteSupport (Descendant E v) :=
      infiniteSupport_mono (fun _ h => h.2) hd
    have hvA := href a v hav hvAmbient
    have hAcofinite : FiniteSupport (fun w => C a w ∧ ¬ Descendant E v w) := by
      rcases hiap a v hav with hfin | hfin
      · exact False.elim (hvA hfin)
      · exact hfin
    obtain ⟨bound, hbound⟩ := (finiteSupport_iff_bounded _).mp hAcofinite
    obtain ⟨w, hcone, hwprod, hlarge⟩ :=
      productive_descendants_unbounded F hForder hFchildren r hFprod bound
    have hBw : B w := by
      rcases hcone with heq | hpath
      · simpa [heq] using hBr
      · cases hpath with
        | edge he => exact he.2.1
        | snoc _ he => exact he.2.1
    have hconeAmbient : w = r ∨ Descendant E r w := by
      rcases hcone with heq | hpath
      · exact Or.inl heq
      · exact Or.inr (ProductiveCore.descendant_mono (fun _ _ he => he.2.2) hpath)
    have hwAmbient : InfiniteSupport (Descendant E w) :=
      infiniteSupport_mono
        (fun _ h => ProductiveCore.descendant_mono (fun _ _ he => he.2.2) h) hwprod
    have hwA := capture_productive_descendant hdir hconv hiap href a r w har hA
      hBw.1 hconeAmbient hwAmbient
    have hsmall := hbound w ⟨hwA, hBw.2⟩
    omega

end DirectedIAPResearch

#print axioms DirectedIAPResearch.bad_founder_productive
#print axioms DirectedIAPResearch.productive_descendants_unbounded
#print axioms DirectedIAPResearch.capture_productive_descendant
#print axioms DirectedIAPResearch.iap_directed_union_of_finite_founders
