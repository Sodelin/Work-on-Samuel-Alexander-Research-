import PedigreeBlockModel
import Mathlib.Data.Sigma.Basic

set_option autoImplicit false

/-!
Observed symbols determine the sharing graph. Injectivity of each block's
parent-symbol assignment is an explicit founder assumption. The graph never
joins different families. For the dependent sum of sampled children, recovery
of the entire family partition is equivalent to connectedness of every
within-family sharing graph. No hidden family labels are supplied to the
estimator: they occur only in the generative model and correctness statement.
-/

namespace PedigreeBlock

universe u v w

variable {Child : Type u} {Family : Type v} {Symbol : Type w} {B : Nat}

def ObservedShare (obs : Child → Fin B → Symbol) (a b : Child) : Prop :=
  a ≠ b ∧ ∃ j, obs a j = obs b j

def display (family : Child → Family) (choices : Child → Code B)
    (symbols : Fin B → Family × Bool → Symbol) (c : Child) (j : Fin B) : Symbol :=
  symbols j (family c, choices c j)

theorem observedShare_symm (obs : Child → Fin B → Symbol) {a b : Child}
    (h : ObservedShare obs a b) : ObservedShare obs b a := by
  rcases h with ⟨hne, j, hj⟩
  exact ⟨Ne.symm hne, j, hj.symm⟩

theorem observedShare_iff (family : Child → Family) (choices : Child → Code B)
    (symbols : Fin B → Family × Bool → Symbol)
    (hinj : ∀ j, Function.Injective (symbols j)) (a b : Child) :
    ObservedShare (display family choices symbols) a b ↔
      a ≠ b ∧ family a = family b ∧ ∃ j, choices a j = choices b j := by
  constructor
  · rintro ⟨hne, j, hj⟩
    have pairEq := hinj j hj
    exact ⟨hne, congrArg Prod.fst pairEq, j, congrArg Prod.snd pairEq⟩
  · rintro ⟨hne, hf, j, hj⟩
    refine ⟨hne, j, ?_⟩
    exact congrArg (symbols j) (Prod.ext hf hj)

theorem observed_path_preserves_family (family : Child → Family)
    (choices : Child → Code B) (symbols : Fin B → Family × Bool → Symbol)
    (hinj : ∀ j, Function.Injective (symbols j)) {a b : Child}
    (h : Relation.ReflTransGen (ObservedShare (display family choices symbols)) a b) :
    family a = family b := by
  induction h with
  | refl => rfl
  | tail _ he ih =>
      exact ih.trans ((observedShare_iff family choices symbols hinj _ _).mp he).2.1

abbrev Children (n : Family → Nat) := (f : Family) × Fin (n f + 1)

def familyChoices {n : Family → Nat} (x : ∀ f, Config (n f) B)
    (c : Children n) : Code B := x c.1 c.2

def familyObservations {n : Family → Nat} (x : ∀ f, Config (n f) B)
    (symbols : Fin B → Family × Bool → Symbol) : Children n → Fin B → Symbol :=
  display Sigma.fst (familyChoices x) symbols

/-- The estimator is the connected-component relation of observed symbols.
Recovery means this relation equals true family membership. -/
def Recovered {n : Family → Nat} (x : ∀ f, Config (n f) B)
    (symbols : Fin B → Family × Bool → Symbol) : Prop :=
  ∀ a b : Children n,
    Relation.ReflTransGen (ObservedShare (familyObservations x symbols)) a b ↔ a.1 = b.1

theorem family_edge_iff {n : Family → Nat} (x : ∀ f, Config (n f) B)
    (symbols : Fin B → Family × Bool → Symbol)
    (hinj : ∀ j, Function.Injective (symbols j))
    (f : Family) (a b : Fin (n f + 1)) :
    ObservedShare (familyObservations x symbols) ⟨f, a⟩ ⟨f, b⟩ ↔ Share (x f) a b := by
  rw [familyObservations, observedShare_iff _ _ _ hinj]
  change ((⟨f, a⟩ : Children n) ≠ (⟨f, b⟩ : Children n) ∧ f = f ∧ ∃ j, x f a j = x f b j) ↔
    (a ≠ b ∧ ∃ j, x f a j = x f b j)
  constructor
  · rintro ⟨hne, _, hj⟩
    exact ⟨fun h => hne (congrArg (fun i : Fin (n f + 1) => (⟨f, i⟩ : Children n)) h), hj⟩
  · rintro ⟨hne, hj⟩
    exact ⟨fun h => hne (sigma_mk_injective (β := fun g : Family => Fin (n g + 1)) h), rfl, hj⟩

theorem family_path_iff {n : Family → Nat} (x : ∀ f, Config (n f) B)
    (symbols : Fin B → Family × Bool → Symbol)
    (hinj : ∀ j, Function.Injective (symbols j))
    (f : Family) (a b : Fin (n f + 1)) :
    Relation.ReflTransGen (ObservedShare (familyObservations x symbols))
      (⟨f, a⟩ : Children n) ⟨f, b⟩ ↔
      Relation.ReflTransGen (Share (x f)) a b := by
  constructor
  · intro h
    have back (c : Children n)
        (hc : Relation.ReflTransGen (ObservedShare (familyObservations x symbols))
          (⟨f, a⟩ : Children n) c) :
        ∃ i, c = (⟨f, i⟩ : Children n) ∧ Relation.ReflTransGen (Share (x f)) a i := by
      induction hc with
      | refl => exact ⟨a, rfl, .refl⟩
      | @tail c d _ edge ih =>
          rcases ih with ⟨i, rfl, hi⟩
          rcases d with ⟨g, j⟩
          have fg : f = g :=
            ((observedShare_iff Sigma.fst (familyChoices x) symbols hinj _ _).mp edge).2.1
          subst g
          exact ⟨j, rfl, hi.tail ((family_edge_iff x symbols hinj f i j).mp edge)⟩
    obtain ⟨i, heq, hi⟩ := back ⟨f, b⟩ h
    have hbi : b = i := sigma_mk_injective (β := fun g : Family => Fin (n g + 1)) heq
    simpa only [hbi] using hi
  · intro h
    induction h with
    | refl => exact .refl
    | @tail i j _ edge ih =>
        exact ih.tail ((family_edge_iff x symbols hinj f i j).mpr edge)

/-- Exact recovery of the observed component partition is equivalent to
connectedness of every actual family's local sharing graph. -/
theorem recovered_iff_connected {n : Family → Nat} (x : ∀ f, Config (n f) B)
    (symbols : Fin B → Family × Bool → Symbol)
    (hinj : ∀ j, Function.Injective (symbols j)) :
    Recovered x symbols ↔ ∀ f, Connected (x f) := by
  constructor
  · intro h f a b
    exact (family_path_iff x symbols hinj f a b).mp ((h ⟨f, a⟩ ⟨f, b⟩).mpr rfl)
  · intro h a b
    constructor
    · exact observed_path_preserves_family Sigma.fst (familyChoices x) symbols hinj
    · rcases a with ⟨f, i⟩
      rcases b with ⟨g, j⟩
      intro hfg
      change f = g at hfg
      subst g
      exact (family_path_iff x symbols hinj f i j).mpr (h f i j)

end PedigreeBlock

#print axioms PedigreeBlock.observedShare_iff
#print axioms PedigreeBlock.observed_path_preserves_family
#print axioms PedigreeBlock.family_path_iff
#print axioms PedigreeBlock.recovered_iff_connected
