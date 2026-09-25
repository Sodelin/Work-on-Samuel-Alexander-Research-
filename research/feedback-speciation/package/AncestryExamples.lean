import AncestryMixing

/-!
Concrete nonvacuity and component uniqueness for the conditional ancestry theorem.
These models are mathematical pedigrees, not empirical population models.
-/
namespace AncestryMixing
open SpeciesBridge SpeciesGlobalIAP

namespace Pedigree

/-- The representative component is unique, although its representative need not be. -/
theorem component_unique_mod_finite {k : Nat} (G : Pedigree k) {S : NatSet}
    (hS : InfiniteSupport S) {a b : Fin k}
    (ha : FiniteSupport (fun v => S v ∧ ¬ G.SameComponent a (G.deme v)))
    (hb : FiniteSupport (fun v => S v ∧ ¬ G.SameComponent b (G.deme v))) :
    G.SameComponent a b := by
  classical
  by_contra hab
  apply hS
  apply finiteSupport_mono (T := fun v =>
      (S v ∧ ¬ G.SameComponent a (G.deme v)) ∨
      (S v ∧ ¬ G.SameComponent b (G.deme v))) ?_ (finiteSupport_union ha hb)
  intro v hv
  by_cases hav : G.SameComponent a (G.deme v)
  · have hnbv : ¬ G.SameComponent b (G.deme v) := by
      intro hbv
      exact hab ⟨hav.1.trans hbv.2, hbv.1.trans hav.2⟩
    exact Or.inr ⟨hv, hnbv⟩
  · exact Or.inl ⟨hv, hav⟩

end Pedigree

namespace Examples

def generation (v : Nat) : Nat := v / 2

def deme (v : Nat) : Fin 2 := ⟨v % 2, Nat.mod_lt _ (by decide)⟩

def organism (n : Nat) (a : Fin 2) : Nat := 2 * n + a.val

@[simp] theorem generation_organism (n : Nat) (a : Fin 2) :
    generation (organism n a) = n := by
  have := a.isLt
  dsimp [generation, organism]
  omega

@[simp] theorem deme_organism (n : Nat) (a : Fin 2) :
    deme (organism n a) = a := by
  apply Fin.ext
  have := a.isLt
  dsimp [deme, organism]
  omega

/-- A vertical parent in each deme, plus any selected cross-deme edge types. -/
def twoDeme (cross : Fin 2 → Fin 2 → Prop) : Pedigree 2 where
  edge := fun u v => generation v = generation u + 1 ∧
    (deme u = deme v ∨ cross (deme u) (deme v))
  generation := generation
  deme := deme
  finitePast := by
    intro n
    apply (finiteSupport_iff_bounded _).mpr
    refine ⟨2 * n, ?_⟩
    intro v hv
    dsimp [generation] at hv
    omega
  occupied := by
    intro n a
    exact ⟨organism n a, generation_organism n a, deme_organism n a⟩
  edgeStep := fun _ _ h => h.1
  ownParent := by
    intro v hv
    refine ⟨organism (generation v - 1) (deme v), ⟨?_, Or.inl ?_⟩, ?_⟩
    · simp only [generation_organism]
      omega
    · exact deme_organism _ _
    · exact deme_organism _ _
  lag := 1
  lagPositive := by decide
  localMix := by
    intro u v hgen hd
    exact .edge ⟨⟨hgen, Or.inl hd.symm⟩, hd.symm⟩

/-- Every selected contact type is recurrent; there are no hidden extra types. -/
theorem recurrent_twoDeme_iff (cross : Fin 2 → Fin 2 → Prop) (a b : Fin 2) :
    (twoDeme cross).Recurrent a b ↔ a = b ∨ cross a b := by
  constructor
  · intro h
    obtain ⟨u, v, _, hu, hv, he⟩ := h 0
    change generation v = generation u + 1 ∧
      (deme u = deme v ∨ cross (deme u) (deme v)) at he
    change deme u = a at hu
    change deme v = b at hv
    simpa only [hu, hv] using he.2
  · intro h N
    refine ⟨organism N a, organism (N + 1) b, ?_, ?_, ?_, ?_⟩
    · change N ≤ generation (organism N a)
      simp
    · exact deme_organism _ _
    · exact deme_organism _ _
    · change generation (organism (N + 1) b) = generation (organism N a) + 1 ∧
        (deme (organism N a) = deme (organism (N + 1) b) ∨
          cross (deme (organism N a)) (deme (organism (N + 1) b)))
      simpa only [generation_organism, deme_organism, true_and] using h

def OneWay (a b : Fin 2) : Prop := a = 0 ∧ b = 1

def Bidirectional (a b : Fin 2) : Prop := a ≠ b

private theorem oneWay_recurrent_nondecreasing {a b : Fin 2}
    (h : (twoDeme OneWay).Recurrent a b) : a.val ≤ b.val := by
  rcases (recurrent_twoDeme_iff OneWay a b).mp h with h | h
  · subst b; exact Nat.le_refl _
  · obtain ⟨ha, hb⟩ := h
    subst a
    subst b
    decide

private theorem oneWay_walk_nondecreasing {a b : Fin 2}
    (h : Walk (twoDeme OneWay).Recurrent a b) : a.val ≤ b.val := by
  induction h with
  | refl => exact Nat.le_refl _
  | snoc _ he ih => exact Nat.le_trans ih (oneWay_recurrent_nondecreasing he)

/-- Recurring one-way parenthood does not give global IAP. -/
theorem oneWay_not_iap : ¬ IAP (twoDeme OneWay).edge Whole := by
  intro h
  have hstrong := (twoDeme OneWay).whole_iap_iff_recurrent_strongly_connected.mp h
  have himpossible := oneWay_walk_nondecreasing (hstrong 1 0)
  change 1 ≤ 0 at himpossible
  omega

/-- Recurring parenthood in both directions gives global IAP in this model. -/
theorem bidirectional_iap : IAP (twoDeme Bidirectional).edge Whole := by
  apply (twoDeme Bidirectional).whole_iap_iff_recurrent_strongly_connected.mpr
  intro a b
  apply Walk.snoc (Walk.refl a)
  apply (recurrent_twoDeme_iff Bidirectional a b).mpr
  by_cases h : a = b
  · exact Or.inl h
  · exact Or.inr h

theorem explicit_pedigree_exists : Nonempty (Pedigree 2) := ⟨twoDeme OneWay⟩

end Examples
end AncestryMixing

#print axioms AncestryMixing.Pedigree.component_unique_mod_finite
#print axioms AncestryMixing.Examples.twoDeme
#print axioms AncestryMixing.Examples.recurrent_twoDeme_iff
#print axioms AncestryMixing.Examples.oneWay_not_iap
#print axioms AncestryMixing.Examples.bidirectional_iap
#print axioms AncestryMixing.Examples.explicit_pedigree_exists