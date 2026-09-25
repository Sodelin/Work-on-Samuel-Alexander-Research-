import Mathlib.Order.Zorn
import DirectedIAP
import RealFounderWindow

/-! Maximal extensions use exactly the same window and reflection constraints
for the candidate and every competitor. This module first works with vertices
already indexed in strict edge order; birth times remain literal real values. -/
namespace FounderMaximal
open SpeciesBridge SpeciesGlobalIAP FounderWindowResearch

theorem weakReach_mono {E : Graph} {S T : NatSet}
    (hST : ∀ v, S v → T v) {a b : Nat} (h : WeakReach E S a b) :
    WeakReach E T a b := by
  induction h with
  | refl hu => exact .refl (hST _ hu)
  | edge hu hv he => exact .edge (hST _ hu) (hST _ hv) he
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

theorem directed_union_connected {E : Graph} {I : Type} [Nonempty I]
    {C : I → NatSet} (hdir : Directed C)
    (hconn : ∀ i, WeaklyConnected E (C i)) : WeaklyConnected E (Union C) := by
  constructor
  · obtain ⟨i⟩ := ‹Nonempty I›
    obtain ⟨v, hv⟩ := (hconn i).1
    exact ⟨v, i, hv⟩
  · intro u v hu hv
    obtain ⟨i, hi⟩ := hu
    obtain ⟨j, hj⟩ := hv
    obtain ⟨k, hik, hjk⟩ := hdir i j
    exact weakReach_mono (fun w hw => ⟨k, hw⟩)
      ((hconn k).2 u v (hik u hi) (hjk v hj))

theorem union_reflection {E : Graph} {I : Type} {C : I → NatSet}
    (href : ∀ i, Reflection E (C i)) : Reflection E (Union C) := by
  intro v hv hinf
  obtain ⟨i, hi⟩ := hv
  exact infiniteSupport_mono (fun w hw => ⟨⟨i, hw.1⟩, hw.2⟩)
    (href i v hi hinf)

/-- Membership in the class whose maximal elements we seek. -/
def WindowSpecies (E : Graph) (birth : Nat → ℝ) (duration : ℝ)
    (S : NatSet) : Prop :=
  Specieslike E S ∧ Reflection E S ∧ RealFounderWindow.Window E birth duration S

/-- Maximality is constrained: all competitors must satisfy the same class. -/
def MaximalWindowSpecies (E : Graph) (birth : Nat → ℝ) (duration : ℝ)
    (S : NatSet) : Prop :=
  WindowSpecies E birth duration S ∧
    ∀ T, (∀ v, S v → T v) → WindowSpecies E birth duration T → ∀ v, T v → S v

theorem windowSpecies_directed_union {E : Graph} {birth : Nat → ℝ}
    (horder : ∀ a b, E a b → a < b)
    (hchildren : ∀ a, FiniteSupport (E a))
    (finite : RealFounderWindow.StrictFiniteSublevels birth)
    {duration : ℝ} {I : Type} [Nonempty I] {C : I → NatSet}
    (hdir : Directed C) (hC : ∀ i, WindowSpecies E birth duration (C i)) :
    WindowSpecies E birth duration (Union C) := by
  have hwindow := RealFounderWindow.window_directed_union finite hdir (fun i => (hC i).2.2)
  refine ⟨⟨directed_union_connected hdir (fun i => (hC i).1.1), ?_,
    DirectedIAPResearch.directed_union_convex hdir (fun i => (hC i).1.2.2)⟩,
    union_reflection (fun i => (hC i).2.1), hwindow⟩
  exact DirectedIAPResearch.iap_directed_union_of_finite_founders horder hchildren
    hdir (fun i => (hC i).1.2.2) (fun i => (hC i).1.2.1)
    (fun i => (hC i).2.1) (RealFounderWindow.window_finite_founders finite hwindow)

/-- A reusable Zorn step for predicates closed under nonempty directed unions. -/
theorem maximal_extension_of_directed_union (P : NatSet → Prop)
    (hclosed : ∀ {I : Type} [Nonempty I] (C : I → NatSet),
      Directed C → (∀ i, P (C i)) → P (Union C))
    (S : NatSet) (hS : P S) :
    ∃ M, (∀ v, S v → M v) ∧ P M ∧
      ∀ T, (∀ v, M v → T v) → P T → ∀ v, T v → M v := by
  classical
  have hchains : ∀ c ⊆ {T : Set Nat | P T}, IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ ub ∈ {T : Set Nat | P T}, ∀ s ∈ c, s ⊆ ub := by
    intro c hc hchain hn
    let C : c → NatSet := fun i => i.val
    haveI : Nonempty c := by
      obtain ⟨s, hs⟩ := hn
      exact ⟨⟨s, hs⟩⟩
    have hdir : Directed C := by
      intro i j
      by_cases hij : i.val = j.val
      · exact ⟨i, fun _ hv => hv, fun v hv => by simpa [C, hij] using hv⟩
      · rcases hchain i.property j.property hij with hij | hji
        · exact ⟨j, fun _ hv => hij hv, fun _ hv => hv⟩
        · exact ⟨i, fun _ hv => hv, fun _ hv => hji hv⟩
    refine ⟨Union C, hclosed C hdir (fun i => hc i.property), ?_⟩
    intro s hs v hv
    exact ⟨⟨s, hs⟩, hv⟩
  obtain ⟨M, hSM, hmax⟩ := zorn_subset_nonempty {T : Set Nat | P T} hchains S hS
  exact ⟨M, fun _ hv => hSM hv, hmax.1, fun T hMT hT v hv => hmax.2 hT hMT hv⟩

/-- Every existing real-window member extends to a maximal member when the
vertex indexing is strict along edges. No per-vertex seed is assumed here. -/
theorem maximal_window_extension_ordered {E : Graph} {birth : Nat → ℝ}
    (horder : ∀ a b, E a b → a < b)
    (hchildren : ∀ a, FiniteSupport (E a))
    (finite : RealFounderWindow.StrictFiniteSublevels birth)
    (duration : ℝ) (S : NatSet) (hS : WindowSpecies E birth duration S) :
    ∃ M, (∀ v, S v → M v) ∧ MaximalWindowSpecies E birth duration M := by
  exact maximal_extension_of_directed_union (WindowSpecies E birth duration)
    (fun C hdir hC => windowSpecies_directed_union horder hchildren finite hdir hC) S hS

end FounderMaximal
#print axioms FounderMaximal.directed_union_connected
#print axioms FounderMaximal.union_reflection
#print axioms FounderMaximal.windowSpecies_directed_union
#print axioms FounderMaximal.maximal_extension_of_directed_union
#print axioms FounderMaximal.maximal_window_extension_ordered
