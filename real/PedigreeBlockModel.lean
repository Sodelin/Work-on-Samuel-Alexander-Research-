import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Relation

set_option autoImplicit false

/-!
A fixed, one-generation founder model. Every child independently chooses one
of two distinct parental symbols at each block. Independence is imposed by
the probability module, not by these deterministic definitions. There are
n+1 children and B observed blocks. This is not the marked ARG observation
law and not the multigeneration REC-GEN theorem.
-/

namespace PedigreeBlock

abbrev Code (B : Nat) := Fin B → Bool
abbrev Config (n B : Nat) := Fin (n + 1) → Code B

def complement {B : Nat} (v : Code B) : Code B := fun b => !(v b)

@[simp] theorem complement_apply {B : Nat} (v : Code B) (b : Fin B) :
    complement v b = !(v b) := rfl

@[simp] theorem complement_complement {B : Nat} (v : Code B) :
    complement (complement v) = v := by
  funext b
  simp

theorem complement_ne {B : Nat} (hB : 0 < B) (v : Code B) :
    complement v ≠ v := by
  intro h
  have h0 := congrFun h (⟨0, hB⟩ : Fin B)
  simp only [complement_apply] at h0
  cases hv : v (⟨0, hB⟩ : Fin B) <;> simp [hv] at h0

/-- A positive pair-sharing edge; distinct children agree in some block. -/
def Share {n B : Nat} (x : Config n B) (a b : Fin (n + 1)) : Prop :=
  a ≠ b ∧ ∃ j, x a j = x b j

/-- All children lie in one connected component of the observed-sharing graph. -/
def Connected {n B : Nat} (x : Config n B) : Prop :=
  ∀ a b, Relation.ReflTransGen (Share x) a b

/-- An anchored description of the exceptional inheritance configurations.
Every vector is the first child's vector or its complement, and the latter
also occurs. With a positive block count the two vectors are distinct. -/
def Bad {n B : Nat} (x : Config n B) : Prop :=
  (∀ i, x i = x 0 ∨ x i = complement (x 0)) ∧
    ∃ i, x i = complement (x 0)

end PedigreeBlock
