import PedigreeBlockModel
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Tactic.NormNum

set_option autoImplicit false

/-!
# Exact probability of the exceptional one-generation family configuration

The probability law is uniform on every child/block bit array. The exceptional
mass is derived from an explicit finite bijection, not inserted as an axiom or
probability parameter. This model is separate from the continuous ARG law.
-/

namespace PedigreeBlock
open MeasureTheory
open scoped ENNReal BigOperators Classical
noncomputable section

abbrev NonzeroTail (n : ℕ) := {t : Fin n → Bool // t ≠ fun _ => false}

def encodeBad {n B : ℕ} (v : Code B) (t : Fin n → Bool) : Config n B :=
  Fin.cases v (fun i => if t i then complement v else v)

def decodeTail {n B : ℕ} (x : Config n B) : Fin n → Bool :=
  fun i => decide (x i.succ = complement (x 0))

theorem encodeBad_zero {n B : ℕ} (v : Code B) (t : Fin n → Bool) :
    encodeBad v t 0 = v := rfl

theorem encodeBad_succ {n B : ℕ} (v : Code B) (t : Fin n → Bool) (i : Fin n) :
    encodeBad v t i.succ = if t i then complement v else v := rfl

theorem encodeBad_bad {n B : ℕ} (v : Code B) (t : NonzeroTail n) :
    Bad (encodeBad v t.val) := by
  constructor
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Or.inl rfl
    · cases ht : t.val j <;> simp [encodeBad, ht]
  · have ht : ¬ ∀ i, t.val i = false := fun h => t.property (funext h)
    obtain ⟨i, hi⟩ := not_forall.mp ht
    have hit : t.val i = true := by cases h : t.val i <;> simp_all
    exact ⟨i.succ, by simp [encodeBad, hit]⟩

theorem decodeTail_nonzero {n B : ℕ} (hB : 0 < B) (x : Config n B) (hx : Bad x) :
    decodeTail x ≠ fun _ => false := by
  intro h
  have hnone : ∀ i, x i ≠ complement (x 0) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (complement_ne hB (x 0)).symm
    · intro hi
      have hh := congrFun h j
      simp [decodeTail, hi] at hh
  obtain ⟨i, hi⟩ := hx.2
  exact hnone i hi

theorem decodeTail_encodeBad {n B : ℕ} (hB : 0 < B)
    (v : Code B) (t : Fin n → Bool) : decodeTail (encodeBad v t) = t := by
  funext i
  cases ht : t i <;> simp [decodeTail, encodeBad, ht, (complement_ne hB v).symm]

theorem encodeBad_decodeTail {n B : ℕ} (hB : 0 < B)
    (x : Config n B) (hx : Bad x) : encodeBad (x 0) (decodeTail x) = x := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rcases hx.1 j.succ with hi | hi
    · simp [encodeBad, decodeTail, hi, (complement_ne hB (x 0)).symm]
    · simp [encodeBad, decodeTail, hi]

/-- Anchor the first child's code and record which later children use its
complement. A nonzero tail ensures both complementary values occur. -/
def badEquiv (n B : ℕ) (hB : 0 < B) :
    {x : Config n B // Bad x} ≃ Code B × NonzeroTail n where
  toFun x := (x.val 0, ⟨decodeTail x.val, decodeTail_nonzero hB x.val x.property⟩)
  invFun p := ⟨encodeBad p.1 p.2.val, encodeBad_bad p.1 p.2⟩
  left_inv x := Subtype.ext (encodeBad_decodeTail hB x.val x.property)
  right_inv p := by
    apply Prod.ext
    · rfl
    · exact Subtype.ext (decodeTail_encodeBad hB p.1 p.2.val)

theorem code_card (B : ℕ) : Fintype.card (Code B) = 2 ^ B := by
  simp [Code]

theorem config_card (n B : ℕ) : Fintype.card (Config n B) = 2 ^ (B * (n + 1)) := by
  simp [Config, ← pow_mul]

theorem nonzeroTail_card (n : ℕ) : Fintype.card (NonzeroTail n) = 2 ^ n - 1 := by
  change Fintype.card {t : Code n // ¬ t = (fun _ => false)} = _
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, code_card]

theorem bad_card (n B : ℕ) (hB : 0 < B) :
    Fintype.card {x : Config n B // Bad x} = 2 ^ B * (2 ^ n - 1) := by
  rw [Fintype.card_congr (badEquiv n B hB), Fintype.card_prod,
    code_card, nonzeroTail_card]

/-- Every labeled child/block bit array has the same PMF mass. -/
def configPMF (n B : ℕ) : PMF (Config n B) := PMF.uniformOfFintype (Config n B)

def configLaw (n B : ℕ) : Measure (Config n B) := (configPMF n B).toMeasure

instance configLaw_probability (n B : ℕ) : IsProbabilityMeasure (configLaw n B) := by
  unfold configLaw
  infer_instance

theorem configPMF_mass (n B : ℕ) (x : Config n B) :
    configPMF n B x = ((2 : ℝ≥0∞) ^ (B * (n + 1)))⁻¹ := by
  simp [configPMF, ← pow_mul]

theorem bad_probability_card (n B : ℕ) (hB : 0 < B) :
    configLaw n B {x | Bad x} =
      ((2 ^ B * (2 ^ n - 1) : ℕ) : ℝ≥0∞) / ((2 ^ (B * (n + 1)) : ℕ) : ℝ≥0∞) := by
  calc
    configLaw n B {x | Bad x} =
      (Fintype.card {x : Config n B // Bad x} : ℝ≥0∞) /
        (Fintype.card (Config n B) : ℝ≥0∞) :=
      PMF.toMeasure_uniformOfFintype_apply {x | Bad x} (Set.toFinite _).measurableSet
    _ = _ := by rw [bad_card n B hB, config_card]

/-- Exact exceptional probability, including the singleton-family case n=0. -/
theorem bad_probability (n B : ℕ) (hB : 0 < B) :
    configLaw n B {x | Bad x} = ((2 ^ n - 1 : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ (B * n) := by
  rw [bad_probability_card n B hB]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.mul_add, Nat.mul_one, pow_add]
  rw [mul_comm ((2 : ℝ≥0∞) ^ B)]
  exact ENNReal.mul_div_mul_right _ _ (pow_ne_zero _ (by norm_num))
    (ENNReal.pow_ne_top (by norm_num))

/-- Finite uniform function sampling gives a product law for coordinate
events. This also proves the independence used for different families. -/
theorem uniform_pi_event {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSingletonClass (α i)]
    (p : ∀ i, α i → Prop) :
    (PMF.uniformOfFintype (∀ i, α i)).toMeasure {x | ∀ i, p i (x i)} =
      ∏ i, (PMF.uniformOfFintype (α i)).toMeasure {a | p i a} := by
  have hc : Fintype.card {x : ∀ i, α i // ∀ i, p i (x i)} =
      ∏ i, Fintype.card {a : α i // p i a} := by
    rw [Fintype.card_congr (Equiv.subtypePiEquivPi (p := p)), Fintype.card_pi]
  calc
    (PMF.uniformOfFintype (∀ i, α i)).toMeasure {x | ∀ i, p i (x i)} =
      (Fintype.card {x : ∀ i, α i // ∀ i, p i (x i)} : ℝ≥0∞) /
        (Fintype.card (∀ i, α i) : ℝ≥0∞) :=
      PMF.toMeasure_uniformOfFintype_apply _ (Set.toFinite _).measurableSet
    _ = (∏ i, (Fintype.card {a : α i // p i a} : ℝ≥0∞)) /
        (∏ i, (Fintype.card (α i) : ℝ≥0∞)) := by
      rw [hc, Fintype.card_pi]
      simp only [Nat.cast_prod]
    _ = ∏ i, (Fintype.card {a : α i // p i a} : ℝ≥0∞) /
        (Fintype.card (α i) : ℝ≥0∞) := by
      symm
      exact ENNReal.prod_div_distrib_of_ne_top (fun i _ => ENNReal.natCast_ne_top _)
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i hi
      exact (PMF.toMeasure_uniformOfFintype_apply _ (Set.toFinite _).measurableSet).symm

/-- The finite uniform configuration law really is independent fair sampling
of every child/block bit: every coordinate-event cylinder factorizes. -/
theorem config_bit_cylinder (n B : ℕ) (p : Fin (n + 1) → Fin B → Bool → Prop) :
    configLaw n B {x | ∀ i b, p i b (x i b)} =
      ∏ i, ∏ b, (PMF.uniformOfFintype Bool).toMeasure {a | p i b a} := by
  unfold configLaw configPMF
  have houter := uniform_pi_event (ι := Fin (n + 1)) (α := fun _ => Code B)
    (fun i (v : Code B) => ∀ b, p i b (v b))
  have hinner : ∀ i : Fin (n + 1),
      (PMF.uniformOfFintype (Code B)).toMeasure {v | ∀ b, p i b (v b)} =
        ∏ b, (PMF.uniformOfFintype Bool).toMeasure {a | p i b a} := by
    intro i
    exact uniform_pi_event (ι := Fin B) (α := fun _ => Bool) (p i)
  exact houter.trans (Finset.prod_congr rfl (fun i _ => hinner i))

theorem fair_bit_singleton (a : Bool) :
    (PMF.uniformOfFintype Bool).toMeasure {a} = (2 : ℝ≥0∞)⁻¹ := by
  rw [PMF.toMeasure_uniformOfFintype_apply _ (measurableSet_singleton a)]
  simp

theorem good_probability (n B : ℕ) (hB : 0 < B) :
    configLaw n B {x | ¬ Bad x} =
      1 - ((2 ^ n - 1 : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ (B * n) := by
  have h := measure_compl ((Set.toFinite {x : Config n B | Bad x}).measurableSet)
    (measure_ne_top (configLaw n B) {x | Bad x})
  simpa only [Set.compl_ofPred, measure_univ, bad_probability n B hB] using h

/-- All families are sampled from one uniform finite function space, so
their independence is proved by counting rather than assumed separately. -/
def familyLaw {ι : Type*} [Fintype ι] (n : ι → ℕ) (B : ℕ) :
    Measure (∀ i, Config (n i) B) :=
  (PMF.uniformOfFintype (∀ i, Config (n i) B)).toMeasure

instance familyLaw_probability {ι : Type*} [Fintype ι] (n : ι → ℕ) (B : ℕ) :
    IsProbabilityMeasure (familyLaw n B) := by
  unfold familyLaw
  infer_instance

theorem family_event_product {ι : Type*} [Fintype ι] (n : ι → ℕ) (B : ℕ)
    (p : ∀ i, Config (n i) B → Prop) :
    familyLaw n B {x | ∀ i, p i (x i)} = ∏ i, configLaw (n i) B {x | p i x} :=
  uniform_pi_event p

theorem families_good_probability {ι : Type*} [Fintype ι]
    (n : ι → ℕ) (B : ℕ) (hB : 0 < B) :
    familyLaw n B {x | ∀ i, ¬ Bad (x i)} =
      ∏ i, (1 - ((2 ^ (n i) - 1 : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ (B * n i)) := by
  calc
    _ = ∏ i, configLaw (n i) B {x | ¬ Bad x} :=
      family_event_product n B (fun _ x => ¬ Bad x)
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i hi
      exact good_probability (n i) B hB

#print axioms badEquiv
#print axioms bad_card
#print axioms configLaw_probability
#print axioms configPMF_mass
#print axioms bad_probability
#print axioms uniform_pi_event
#print axioms config_bit_cylinder
#print axioms fair_bit_singleton
#print axioms good_probability
#print axioms familyLaw_probability
#print axioms family_event_product
#print axioms families_good_probability

end
end PedigreeBlock
