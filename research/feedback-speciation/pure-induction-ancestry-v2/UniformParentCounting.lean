import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

/-!
Finite-prefix normalized counting for independent uniform ordered parent draws.
Each of N children has two ordered parent slots; draws are with replacement.
This file does not construct an infinite product probability measure, and it
makes no assertion that a frequency mixing coefficient specifies these draws.
-/
namespace UniformParentCounting

/-- A complete one-generation parent assignment: child, slot, parent. -/
abbrev ParentTable (N : ℕ) := Fin N → Fin 2 → Fin N

/-- The designated parents are distinct when N is at least two. -/
def parentZero {N : ℕ} (hN : 2 ≤ N) : Fin N := ⟨0, by omega⟩
def parentOne {N : ℕ} (hN : 2 ≤ N) : Fin N := ⟨1, by omega⟩

theorem designated_parents_distinct {N : ℕ} (hN : 2 ≤ N) :
    parentZero hN ≠ parentOne hN := by
  intro h
  have hv := congrArg Fin.val h
  norm_num [parentZero, parentOne] at hv

/-- Every child chooses parent 0 in slot 0 and parent 1 in slot 1. -/
def designatedTable {N : ℕ} (hN : 2 ≤ N) : ParentTable N :=
  fun _ slot => ⟨slot.val, lt_of_lt_of_le slot.isLt hN⟩

theorem designated_table_pair {N : ℕ} (hN : 2 ≤ N) (child : Fin N) :
    designatedTable hN child 0 = parentZero hN ∧
    designatedTable hN child 1 = parentOne hN := by
  constructor <;> rfl

/-- The event specifies both ordered slots for every child. -/
def IsDesignated {N : ℕ} (hN : 2 ≤ N) (t : ParentTable N) : Prop :=
  ∀ child, t child 0 = parentZero hN ∧ t child 1 = parentOne hN

theorem isDesignated_iff {N : ℕ} (hN : 2 ≤ N) (t : ParentTable N) :
    IsDesignated hN t ↔ t = designatedTable hN := by
  constructor
  · intro h
    funext child slot
    have hs : slot = 0 ∨ slot = 1 := by
      have hv : slot.val = 0 ∨ slot.val = 1 := by omega
      rcases hv with hv | hv
      · exact Or.inl (Fin.ext hv)
      · exact Or.inr (Fin.ext hv)
    rcases hs with rfl | rfl
    · exact (h child).1
    · exact (h child).2
  · rintro rfl
    exact designated_table_pair hN

/-- Number of all possible ordered parent tables. -/
def tableCount (N : ℕ) : ℕ := N ^ (2 * N)

theorem card_parent_tables (N : ℕ) :
    Fintype.card (ParentTable N) = tableCount N := by
  simp only [ParentTable, Fintype.card_fun, Fintype.card_fin, tableCount, pow_mul]

theorem tableCount_pos {N : ℕ} (hN : 2 ≤ N) : 0 < tableCount N := by
  exact pow_pos (by omega) _

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Exactly one table realizes the designated ordered pair for every child. -/
theorem card_designated {N : ℕ} (hN : 2 ≤ N) :
    Fintype.card {t : ParentTable N // IsDesignated hN t} = 1 := by
  let e : {t : ParentTable N // IsDesignated hN t} ≃ Unit :=
    { toFun := fun _ => Unit.unit
      invFun := fun _ => ⟨designatedTable hN, designated_table_pair hN⟩
      left_inv := fun t => Subtype.ext ((isDesignated_iff hN t.val).mp t.property).symm
      right_inv := by intro u; cases u; rfl }
  calc
    _ = Fintype.card Unit := Fintype.card_congr e
    _ = 1 := Fintype.card_unique

theorem card_nondesignated {N : ℕ} (hN : 2 ≤ N) :
    Fintype.card {t : ParentTable N // t ≠ designatedTable hN} = tableCount N - 1 := by
  rw [Fintype.card_subtype_compl (fun t : ParentTable N => t = designatedTable hN),
    Fintype.card_subtype_eq, card_parent_tables]

/-- A finite generation sequence that never realizes the designated table. -/
abbrev AvoidingSequence {N : ℕ} (hN : 2 ≤ N) (k : ℕ) :=
  {ts : Fin k → ParentTable N // ∀ i, ts i ≠ designatedTable hN}

/-- Avoidance is a coordinatewise restriction, with no assumed count. -/
def avoidingEquiv {N : ℕ} (hN : 2 ≤ N) (k : ℕ) :
    AvoidingSequence hN k ≃
      (Fin k → {t : ParentTable N // t ≠ designatedTable hN}) where
  toFun ts i := ⟨ts.val i, ts.property i⟩
  invFun ts := ⟨fun i => (ts i).val, fun i => (ts i).property⟩
  left_inv ts := by apply Subtype.ext; rfl
  right_inv ts := by funext i; apply Subtype.ext; rfl

theorem card_generation_sequences (N k : ℕ) :
    Fintype.card (Fin k → ParentTable N) = tableCount N ^ k := by
  rw [Fintype.card_fun, Fintype.card_fin, card_parent_tables]

theorem card_avoiding_sequences {N : ℕ} (hN : 2 ≤ N) (k : ℕ) :
    Fintype.card (AvoidingSequence hN k) = (tableCount N - 1) ^ k := by
  rw [Fintype.card_congr (avoidingEquiv hN k), Fintype.card_fun,
    Fintype.card_fin, card_nondesignated]

/-- Uniform probability on the finite set of all k-generation table sequences. -/
def avoidanceProbability {N : ℕ} (hN : 2 ≤ N) (k : ℕ) : ℝ :=
  (Fintype.card (AvoidingSequence hN k) : ℝ) /
    (Fintype.card (Fin k → ParentTable N) : ℝ)

theorem avoidance_probability_exact {N : ℕ} (hN : 2 ≤ N) (k : ℕ) :
    avoidanceProbability hN k =
      (((tableCount N : ℝ) - 1) / (tableCount N : ℝ)) ^ k := by
  have hM : 1 ≤ tableCount N := tableCount_pos hN
  unfold avoidanceProbability
  rw [card_avoiding_sequences, card_generation_sequences, Nat.cast_pow, Nat.cast_pow,
    Nat.cast_sub hM, Nat.cast_one, div_pow]

/-- Uniform one-generation success probability as favorable count / total count. -/
def successProbability {N : ℕ} (hN : 2 ≤ N) : ℝ :=
  (Fintype.card {t : ParentTable N // IsDesignated hN t} : ℝ) /
    (Fintype.card (ParentTable N) : ℝ)

theorem success_probability_exact {N : ℕ} (hN : 2 ≤ N) :
    successProbability hN = 1 / (N : ℝ) ^ (2 * N) := by
  unfold successProbability
  rw [card_designated, card_parent_tables]
  simp only [Nat.cast_one, tableCount, Nat.cast_pow]

theorem success_probability_zpow {N : ℕ} (hN : 2 ≤ N) :
    successProbability hN = (N : ℝ) ^ (-((2 * N : ℕ) : ℤ)) := by
  rw [success_probability_exact]
  simp only [zpow_neg, zpow_natCast, one_div]

theorem success_probability_positive {N : ℕ} (hN : 2 ≤ N) :
    0 < successProbability hN := by
  rw [success_probability_exact]
  exact div_pos (by norm_num) (pow_pos (Nat.cast_pos.mpr (by omega)) _)

end
end UniformParentCounting

#print axioms UniformParentCounting.designated_parents_distinct
#print axioms UniformParentCounting.isDesignated_iff
#print axioms UniformParentCounting.card_parent_tables
#print axioms UniformParentCounting.card_designated
#print axioms UniformParentCounting.card_avoiding_sequences
#print axioms UniformParentCounting.avoidance_probability_exact
#print axioms UniformParentCounting.success_probability_zpow
#print axioms UniformParentCounting.success_probability_positive




