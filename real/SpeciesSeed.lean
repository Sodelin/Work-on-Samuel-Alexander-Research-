import Mathlib.Order.Zorn
import SeedIntersections
import DirectedIAP

/-!
# Genuine per-vertex species seeds

Scratch module. Strict natural chronological edges and finite child sets
suffice. No RootConesIAP hypothesis or source-paper existence axiom is used.

Reverse-inclusion Zorn first minimizes convex reflecting sets whose fixed
member v is a common ancestor. If such a minimum failed IAP, the productive
part of its nondescendant region would be a proper smaller candidate.
-/


namespace SpeciesSeed

open SpeciesBridge SpeciesGlobalIAP SpeciesRootCriterion FounderWindowResearch
open DirectedIAPResearch

/-- The prescribed vertex is retained as common ancestor throughout minimization. -/
def Anchored (E : Graph) (v : Nat) (S : NatSet) : Prop :=
  S v ∧ Convex E S ∧ Reflection E S ∧
    ∀ w, S w → w = v ∨ Descendant E v w

theorem cone_anchored (E : Graph) (v : Nat) : Anchored E v (Cone E v) :=
  ⟨Or.inl rfl, cone_convex E v, cone_reflection E v, fun _ h => h⟩

theorem anchored_commonAncestor {E : Graph} {v : Nat} {S : NatSet}
    (hS : Anchored E v S) : CommonAncestor E S := by
  refine ⟨v, hS.1, ?_⟩
  intro w hw hne
  exact (hS.2.2.2 w hw).resolve_left hne

/-- CA plus ambient convexity supplies connectivity in the induced subgraph. -/
theorem anchored_connected {E : Graph} {v : Nat} {S : NatSet}
    (hS : Anchored E v S) : WeaklyConnected E S := by
  have fromRoot : ∀ w, S w → WeakReach E S v w := by
    intro w hw
    rcases hS.2.2.2 w hw with heq | hd
    · subst w
      exact .refl hS.1
    · exact ProductiveCore.descendant_weakReach_convex hS.2.1 hd hS.1 hw
  refine ⟨⟨v, hS.1⟩, ?_⟩
  intro a b ha hb
  exact .trans (fromRoot a ha).symm (fromRoot b hb)

/-- The genuine minimality step. The lower bounds are actual intersections;
their reflection property is proved from finite branching, not assumed. -/
theorem anchored_minimal_exists (E : Graph)
    (horder : ∀ a b, E a b → a < b)
    (hchildren : ∀ a, FiniteSupport (E a)) (v : Nat) :
    ∃ S : NatSet, Anchored E v S ∧
      ∀ T : NatSet, (∀ w, T w → S w) → Anchored E v T → ∀ w, S w → T w := by
  classical
  let A : Set (Set Nat) := {S | Anchored E v S}
  have lower : ∀ c ⊆ A, IsChain (· ⊆ ·) c →
      ∃ lb ∈ A, ∀ S ∈ c, lb ⊆ S := by
    intro c hc hchain
    by_cases hnonempty : c.Nonempty
    · let C : c → NatSet := fun i => i.val
      letI : Nonempty c := by
        obtain ⟨S, hS⟩ := hnonempty
        exact ⟨⟨S, hS⟩⟩
      have hstage : ∀ i : c, Anchored E v (C i) := fun i => hc i.property
      have hdown : SeedIntersections.DownDirected C := by
        intro i j
        by_cases heq : i.val = j.val
        · refine ⟨i, fun _ h => h, ?_⟩
          intro w hw
          change j.val w
          rw [← heq]
          exact hw
        · rcases hchain i.property j.property heq with hij | hji
          · exact ⟨i, fun _ h => h, fun _ h => hij h⟩
          · exact ⟨j, fun _ h => hji h, fun _ h => h⟩
      let U : NatSet := SeedIntersections.Inter C
      have hU : Anchored E v U := by
        refine ⟨fun i => (hstage i).1, ?_, ?_, ?_⟩
        · intro x ha hd i
          obtain ⟨a, ha, hax⟩ := ha
          obtain ⟨d, hd, hxd⟩ := hd
          exact (hstage i).2.1 x ⟨a, ha i, hax⟩ ⟨d, hd i, hxd⟩
        · exact SeedIntersections.reflection_intersection horder hchildren hdown
            (fun i => (hstage i).2.1) (fun i => (hstage i).2.2.1)
        · intro w hw
          obtain ⟨i⟩ := ‹Nonempty c›
          exact (hstage i).2.2.2 w (hw i)
      refine ⟨U, hU, ?_⟩
      intro S hS w hw
      exact hw ⟨S, hS⟩
    · refine ⟨Cone E v, cone_anchored E v, ?_⟩
      intro S hS
      exact False.elim (hnonempty ⟨S, hS⟩)
  obtain ⟨S, hS⟩ := zorn_superset A lower
  refine ⟨S, hS.1, ?_⟩
  intro T hTS hT
  exact hS.2 hT hTS

/-- Productive vertices in the actual graph induced on B, retaining membership
explicitly. This construction is used only to contradict seed minimality. -/
def ProductivePart (E : Graph) (B : NatSet) : NatSet :=
  fun x => B x ∧ ProductiveCore.Core (ProductiveCore.Induced E B) x

theorem productivePart_convex {E : Graph} {B : NatSet} (hB : Convex E B) :
    Convex E (ProductivePart E B) := by
  intro x ha hd
  obtain ⟨a, ha, hax⟩ := ha
  obtain ⟨d, hd, hxd⟩ := hd
  have hx : B x := hB x ⟨a, ha.1, hax⟩ ⟨d, hd.1, hxd⟩
  refine ⟨hx, ?_⟩
  exact ProductiveCore.core_ancestrallyClosed (ProductiveCore.Induced E B) x d hd.2
    (ProductiveCore.descendant_induced_of_convex hB hxd hx hd.1)

/-- Every member of the productive part has infinitely many descendants in
that same part; this is stronger than the required REF implication. -/
theorem productivePart_internal_infinite (E : Graph)
    (horder : ∀ a b, E a b → a < b)
    (hchildren : ∀ a, FiniteSupport (E a)) (B : NatSet)
    (x : Nat) (hx : ProductivePart E B x) :
    InfiniteSupport (fun w => ProductivePart E B w ∧ Descendant E x w) := by
  let F := ProductiveCore.Induced E B
  have hForder : ∀ a b, F a b → a < b := fun a b he => horder a b he.2.2
  have hFchildren : ∀ a, FiniteSupport (F a) :=
    fun a => finiteSupport_mono (fun _ he => he.2.2) (hchildren a)
  intro hfinite
  obtain ⟨bound, hbound⟩ := (finiteSupport_iff_bounded _).mp hfinite
  obtain ⟨w, hcone, hwcore, hwlarge⟩ :=
    productive_descendants_unbounded F hForder hFchildren x hx.2 (bound + x + 1)
  have hpath : Descendant F x w := by
    rcases hcone with heq | hp
    · subst w
      omega
    · exact hp
  have hBw : B w := by
    cases hpath with
    | edge he => exact he.2.1
    | snoc _ he => exact he.2.1
  have hambient : Descendant E x w :=
    ProductiveCore.descendant_mono (fun _ _ he => he.2.2) hpath
  have hsmall := hbound w ⟨⟨hBw, hwcore⟩, hambient⟩
  omega

theorem productivePart_reflection (E : Graph)
    (horder : ∀ a b, E a b → a < b)
    (hchildren : ∀ a, FiniteSupport (E a)) (B : NatSet) :
    Reflection E (ProductivePart E B) :=
  fun x hx _ => productivePart_internal_infinite E horder hchildren B x hx

/-- Minimal convex reflecting sets with a prescribed common ancestor satisfy
IAP. The bad-region productive part witnesses every purported failure. -/
theorem minimal_anchored_iap (E : Graph)
    (horder : ∀ a b, E a b → a < b)
    (hchildren : ∀ a, FiniteSupport (E a)) (v : Nat) (S : NatSet)
    (hS : Anchored E v S)
    (hminimal : ∀ T : NatSet, (∀ w, T w → S w) →
      Anchored E v T → ∀ w, S w → T w) : IAP E S := by
  classical
  intro w hw
  by_cases hdesc : FiniteSupport (fun z => S z ∧ Descendant E w z)
  · exact Or.inl hdesc
  · apply Or.inr
    apply Classical.byContradiction
    intro hbad
    have hfounders : FiniteSupport (Founder E S) :=
      window_finite_founders (commonAncestor_window horder (anchored_commonAncestor hS) 0)
    obtain ⟨r, hr, hBr, hrprod⟩ :=
      bad_founder_productive horder hS.2.1 hfounders hbad
    have hrv : r = v := by
      rcases hS.2.2.2 r hr.1 with heq | hd
      · exact heq
      · exact False.elim (hr.2 v hS.1 hd)
    subst r
    let B := Bad E S w
    let T := ProductivePart E B
    have hT : Anchored E v T :=
      ⟨⟨hBr, hrprod⟩, productivePart_convex (bad_convex hS.2.1 w),
        productivePart_reflection E horder hchildren B,
        fun z hz => hS.2.2.2 z hz.1.1⟩
    have hST : ∀ z, S z → T z := hminimal T (fun _ hz => hz.1.1) hT
    apply hdesc
    refine ⟨[], ?_⟩
    intro z hz
    exact False.elim ((hST z hz.1).1.2 hz.2)

/-- The stronger anchored seed endpoint, before forgetting the prescribed
common ancestor and packaging connectivity. -/
theorem exists_anchored_seed (E : Graph)
    (horder : ∀ a b, E a b → a < b)
    (hchildren : ∀ a, FiniteSupport (E a)) (v : Nat) :
    ∃ S : NatSet, Anchored E v S ∧ IAP E S := by
  obtain ⟨S, hS, hminimal⟩ := anchored_minimal_exists E horder hchildren v
  exact ⟨S, hS, minimal_anchored_iap E horder hchildren v S hS hminimal⟩

/-- Every vertex belongs to a genuine connected convex IAP+CA+REF seed.
No maximality or RootConesIAP hypothesis is part of the premise. -/
theorem exists_seed (E : Graph)
    (horder : ∀ a b, E a b → a < b)
    (hchildren : ∀ a, FiniteSupport (E a)) (v : Nat) :
    ∃ S : NatSet, S v ∧ Specieslike E S ∧ CommonAncestor E S ∧ Reflection E S := by
  obtain ⟨S, hS, hiap⟩ := exists_anchored_seed E horder hchildren v
  exact ⟨S, hS.1, ⟨anchored_connected hS, hiap, hS.2.1⟩,
    anchored_commonAncestor hS, hS.2.2.1⟩

end SpeciesSeed

#print axioms SpeciesSeed.anchored_minimal_exists
#print axioms SpeciesSeed.productivePart_convex
#print axioms SpeciesSeed.productivePart_internal_infinite
#print axioms SpeciesSeed.minimal_anchored_iap
#print axioms SpeciesSeed.exists_anchored_seed
#print axioms SpeciesSeed.exists_seed

