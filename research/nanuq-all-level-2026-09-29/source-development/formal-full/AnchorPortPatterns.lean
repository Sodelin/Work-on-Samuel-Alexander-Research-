import AnchorComposition
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Finite equality-pattern facts for four taxa projected to arbitrary ports.
These are generic combinatorics, not graph classification assumptions. -/
namespace Nanuq.PortPatterns

open scoped BigOperators

/-- Increasing embedding of the triple obtained by omitting one taxon. -/
def omitTriple (i : Fin 4) : Fin 3 ↪ Fin 4 := Fin.succAboveEmb i

def tripleInjective {P : Type*} (f : Fin 4 → P) (i : Fin 4) : Prop :=
  Function.Injective (fun j => f (omitTriple i j))

instance {P : Type*} [DecidableEq P] (f : Fin 4 → P) (i : Fin 4) :
    Decidable (tripleInjective f i) := by
  unfold tripleInjective Function.Injective
  infer_instance

def tripleCount {P : Type*} [DecidableEq P] (f : Fin 4 → P) : Nat :=
  ∑ i : Fin 4, if tripleInjective f i then 1 else 0

def portCount {P : Type*} [DecidableEq P] (f : Fin 4 → P) : Nat :=
  (Finset.univ.image f).card

theorem injective_fin3_iff {P : Type*} (f : Fin 3 → P) :
    Function.Injective f ↔ f 0 ≠ f 1 ∧ f 0 ≠ f 2 ∧ f 1 ≠ f 2 := by
  constructor
  · intro h
    exact ⟨fun he => (by decide : (0 : Fin 3) ≠ 1) (h he),
      fun he => (by decide : (0 : Fin 3) ≠ 2) (h he),
      fun he => (by decide : (1 : Fin 3) ≠ 2) (h he)⟩
  · rintro ⟨h01,h02,h12⟩ i j hij
    fin_cases i <;> fin_cases j <;> simp_all

@[simp] theorem tripleInjective_zero {P : Type*} (f : Fin 4 → P) :
    tripleInjective f 0 ↔ f 1 ≠ f 2 ∧ f 1 ≠ f 3 ∧ f 2 ≠ f 3 := by
  rw [tripleInjective,injective_fin3_iff]
  rfl

@[simp] theorem tripleInjective_one {P : Type*} (f : Fin 4 → P) :
    tripleInjective f 1 ↔ f 0 ≠ f 2 ∧ f 0 ≠ f 3 ∧ f 2 ≠ f 3 := by
  rw [tripleInjective,injective_fin3_iff]
  rfl

@[simp] theorem tripleInjective_two {P : Type*} (f : Fin 4 → P) :
    tripleInjective f 2 ↔ f 0 ≠ f 1 ∧ f 0 ≠ f 3 ∧ f 1 ≠ f 3 := by
  rw [tripleInjective,injective_fin3_iff]
  rfl

@[simp] theorem tripleInjective_three {P : Type*} (f : Fin 4 → P) :
    tripleInjective f 3 ↔ f 0 ≠ f 1 ∧ f 0 ≠ f 2 ∧ f 1 ≠ f 2 := by
  rw [tripleInjective,injective_fin3_iff]
  rfl
theorem tripleCount_explicit {P : Type*} [DecidableEq P] (f : Fin 4 → P) :
    tripleCount f =
      (if f 1 ≠ f 2 ∧ f 1 ≠ f 3 ∧ f 2 ≠ f 3 then 1 else 0) +
      (if f 0 ≠ f 2 ∧ f 0 ≠ f 3 ∧ f 2 ≠ f 3 then 1 else 0) +
      (if f 0 ≠ f 1 ∧ f 0 ≠ f 3 ∧ f 1 ≠ f 3 then 1 else 0) +
      (if f 0 ≠ f 1 ∧ f 0 ≠ f 2 ∧ f 1 ≠ f 2 then 1 else 0) := by
  have huniv : (Finset.univ : Finset (Fin 4)) = {0,1,2,3} := by decide +kernel
  unfold tripleCount
  rw [huniv,Finset.sum_insert (by decide),Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),Finset.sum_singleton]
  simp only [tripleInjective_zero,tripleInjective_one,tripleInjective_two,tripleInjective_three]
  omega

theorem portCount_explicit {P : Type*} [DecidableEq P] (f : Fin 4 → P) :
    portCount f = ({f 0,f 1,f 2,f 3} : Finset P).card := by
  have huniv : (Finset.univ : Finset (Fin 4)) = {0,1,2,3} := by decide +kernel
  simp [portCount,huniv]

/-- Four occupied ports contribute all four triples; three ports contribute
exactly two; at most two ports contribute none. All equality patterns are
proved, for arbitrary port labels. -/
theorem tripleCount_by_portCount {P : Type*} [DecidableEq P] (f : Fin 4 → P) :
    tripleCount f = if portCount f = 4 then 4 else if portCount f = 3 then 2 else 0 := by
  rw [tripleCount_explicit,portCount_explicit]
  by_cases h01 : f 0 = f 1 <;> by_cases h02 : f 0 = f 2 <;>
    by_cases h03 : f 0 = f 3 <;> by_cases h12 : f 1 = f 2 <;>
    by_cases h13 : f 1 = f 3 <;> by_cases h23 : f 2 = f 3
  all_goals simp_all

theorem tripleCount_cases {P : Type*} [DecidableEq P] (f : Fin 4 → P) :
    tripleCount f = 0 ∨ tripleCount f = 2 ∨ tripleCount f = 4 := by
  rw [tripleCount_by_portCount]
  split_ifs <;> simp

#print axioms tripleCount_by_portCount
#print axioms tripleCount_cases
end Nanuq.PortPatterns