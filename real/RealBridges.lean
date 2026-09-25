import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import SamuelAlexanderResearch.BirthOrder
import SamuelAlexanderResearch.PositiveUnavoidability
import SamuelAlexanderResearch.SharpCorollaries
import SamuelAlexanderResearch.FiniteEditStability
import SamuelAlexanderResearch.PhaseShift
import SamuelAlexanderResearch.PopulationReindex

/-! Literal real-birthdate transport and real-valued sharp coefficients.
Mathlib's Real is the actual Cauchy-completion real type. This optional
project uses the same pinned Lean version as the Std-only core library. -/

namespace RealBridges
open BirthOrder SpeciesBridge BinaryPopulation BinaryAvoidance

universe u

theorem finiteCover_iff_setFinite {V : Type u} (S : V → Prop) :
    BirthOrder.FiniteCover S ↔ Set.Finite {x | S x} := by
  classical
  constructor
  · rintro ⟨xs, hxs⟩
    exact xs.finite_toSet.subset hxs
  · intro h
    exact ⟨h.toFinset.toList, by simp⟩

/-- A binary population on any vertex type with actual real birthdates.
The finite-list encoding of infinitude and finiteness is the core library's;
`finiteCover_iff_setFinite` connects it to Mathlib set finiteness. -/
structure BinaryRealPopulation (V : Type u) where
  edge : V → V → Bool → Prop
  birth : V → ℝ
  infinite : BirthOrder.InfiniteVertices V
  sublevels : ∀ r, BirthOrder.FiniteCover (fun x => birth x ≤ r)
  chronological : ∀ x y b, edge x y b → birth x < birth y
  unique : ∀ x y a b, edge x y a → edge x y b → a = b
  roots : BirthOrder.FiniteCover (fun y => ∀ x b, ¬ edge x y b)
  children : ∀ x, BirthOrder.FiniteCover (fun y => ∃ b, edge x y b)
  parents : ∀ y, ¬ (∀ x b, ¬ edge x y b) → ∀ b, ∃ x, edge x y b

noncomputable def BinaryRealPopulation.enumeration {V : Type u}
    (p : BinaryRealPopulation V) : BirthOrder.OrderedEnumeration p.birth :=
  BirthOrder.orderedEnumeration p.birth p.infinite p.sublevels

def BinaryRealPopulation.reindexed {V : Type u} (p : BinaryRealPopulation V) :
    LabelledGraph := fun i j b => p.edge (p.enumeration.toFun i) (p.enumeration.toFun j) b

theorem BinaryRealPopulation.root_iff {V : Type u} (p : BinaryRealPopulation V)
    (j : Nat) : Root (ForgetLabels p.reindexed) j ↔
      ∀ x b, ¬ p.edge x (p.enumeration.toFun j) b := by
  constructor
  · intro h x b he
    apply h (p.enumeration.index x)
    refine ⟨b, ?_⟩
    simpa only [BinaryRealPopulation.reindexed, p.enumeration.toFun_index] using he
  · intro h i ⟨b, he⟩
    exact h _ b he

/-- All natural-population hypotheses are derived from the actual real model. -/
theorem BinaryRealPopulation.reindexed_population {V : Type u}
    (p : BinaryRealPopulation V) : BinaryNatPopulation p.reindexed := by
  constructor
  · intro i j a b ha hb
    exact p.unique _ _ a b ha hb
  constructor
  · refine ⟨?_, finite_birthdate_prefix, ?_, whole_infinite⟩
    · intro i j ⟨b, he⟩
      exact p.enumeration.edges_increase (fun x y => p.edge x y b)
        (fun x y he => p.chronological x y b he) i j he
    · intro i
      exact p.enumeration.finiteCover_pullback _ (p.children _)
  constructor
  · obtain ⟨xs, hxs⟩ := p.enumeration.finiteCover_pullback _ p.roots
    exact ⟨xs, fun j hj => hxs j ((p.root_iff j).mp hj)⟩
  · intro j hj b
    have hn : ¬ (∀ x a, ¬ p.edge x (p.enumeration.toFun j) a) := by
      intro h
      exact hj ((p.root_iff j).mpr h)
    obtain ⟨x, hx⟩ := p.parents _ hn b
    refine ⟨p.enumeration.index x, ?_⟩
    simpa only [BinaryRealPopulation.reindexed, p.enumeration.toFun_index] using hx

/-- The positive unavoidability theorem for arbitrary real-birthdated vertices,
with no supplied enumeration, countability, or positive-theorem premise. -/
theorem eventuallyPeriodic_realized {V : Type u} (p : BinaryRealPopulation V)
    (s : Nat → Bool) (hs : EventuallyPeriodic s) :
    ∃ path : Nat → V, ∀ k, p.edge (path k) (path (k + 1)) (s k) := by
  obtain ⟨path, hp⟩ := PositiveUnavoidability.eventuallyPeriodic_realized
    s hs p.reindexed p.reindexed_population
  exact ⟨fun k => p.enumeration.toFun (path k), hp⟩

/-- Strict finite real sublevels also give the exact enumeration hypotheses. -/
theorem finite_real_sublevels_of_strict {V : Type u} (birth : V → ℝ)
    (hf : ∀ r, BirthOrder.FiniteCover (fun x => birth x < r)) :
    BirthOrder.FiniteSublevels birth :=
  BirthOrder.finiteSublevels_of_strict birth
    (fun r => ⟨r + 1, by linarith⟩) hf

open SamuelAlexanderResearch.ThueMorseBound SharpThueMorse ThueMorseBits

/-- The real-valued 8/3 upper bound, for every positive-start matching prefix. -/
theorem real_sharp_bound (v ell : Nat) (hv : 1 ≤ v)
    (hp : ∃ w, Reachable t t v ell w) :
    (ell : ℝ) ≤ (8 / 3 : ℝ) * v - 1 / 3 := by
  have hn := sharp_path_bound v ell hv hp
  have hn' : 3 * ell + 1 ≤ 8 * v := by omega
  have hr : (3 : ℝ) * ell + 1 ≤ 8 * v := by exact_mod_cast hn'
  linarith

/-- No smaller real coefficient, with any finite real additive constant,
can bound all maxima. The proof uses the checked dyadic equality family. -/
theorem real_coefficient_optimal (c C : ℝ) (hc : c < 8 / 3) :
    ∃ v ell : Nat, 1 ≤ v ∧ IsMaximumLength t t v ell ∧
      c * v + C < ell := by
  have hgap : 0 < 8 - 3 * c := by linarith
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((C + 3 - c) / (8 - 3 * c))
    (by norm_num : (1 : ℝ) < 2)
  have hm : C + 3 - c < (2 : ℝ)^n * (8 - 3 * c) :=
    (div_lt_iff₀ hgap).mp hn
  have hp := Nat.two_pow_pos n
  refine ⟨3 * 2^n - 1, 8 * 2^n - 3, by omega, sharp_equality_family n, ?_⟩
  have h1 : ((3 * 2^n - 1 : Nat) : ℝ) = 3 * (2 : ℝ)^n - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 3 * 2^n)]
    push_cast
    rfl
  have h2 : ((8 * 2^n - 3 : Nat) : ℝ) = 8 * (2 : ℝ)^n - 3 := by
    rw [Nat.cast_sub (by omega : 3 ≤ 8 * 2^n)]
    push_cast
    rfl
  rw [h1, h2]
  nlinarith

/-- The static comparison in actual real vector spaces: a common point of
two regions is in every normalized binary weighted mix. Nonnegativity is
unnecessary for this inclusion, so it also covers convex weights. -/
theorem real_intersection_subset_weighted_mix
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (A B : Set E) (a b : ℝ) (hab : a + b = 1) :
    A ∩ B ⊆ {x | ∃ u ∈ A, ∃ v ∈ B, x = a • u + b • v} := by
  intro x hx
  exact ⟨x, hx.1, x, hx.2, by rw [← add_smul, hab, one_smul]⟩

/-- The same statement applied to genuine real convex hulls. -/
theorem convex_hull_intersection_subset_weighted_mix
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A B : Set E) (a b : ℝ) (hab : a + b = 1) :
    convexHull ℝ A ∩ convexHull ℝ B ⊆
      {x | ∃ u ∈ convexHull ℝ A, ∃ v ∈ convexHull ℝ B,
        x = a • u + b • v} :=
  real_intersection_subset_weighted_mix _ _ a b hab

open FiniteEditStability QuantitativeAvoidance

/-- Arbitrarily late witnesses within a fixed additive error of slope 8/3
exclude every smaller real coefficient, even with a real additive constant. -/
theorem coefficient_from_late_witnesses (P : Nat → Nat → Prop) (B : Nat)
    (hw : ∀ requested, ∃ v ell, requested ≤ v ∧ P v ell ∧ 8*v ≤ 3*ell+B)
    (c C : ℝ) (hc : c < 8/3) :
    ∃ v ell, P v ell ∧ c*v+C < ell := by
  have hgap : 0 < 8-3*c := by linarith
  obtain ⟨requested, hr⟩ := exists_nat_gt ((3*C+B)/(8-3*c))
  have hr' : 3*C+B < (requested : ℝ)*(8-3*c) := (div_lt_iff₀ hgap).mp hr
  obtain ⟨v, ell, hv, hp, hb⟩ := hw requested
  have hv' : (requested : ℝ) ≤ v := by exact_mod_cast hv
  have hb' : (8 : ℝ)*v ≤ 3*ell+B := by exact_mod_cast hb
  refine ⟨v, ell, hp, ?_⟩
  nlinarith [mul_nonneg (sub_nonneg.mpr hv') (le_of_lt hgap)]

theorem finite_edit_real_bound (s : Nat → Bool) (m : Nat)
    (hag : AgreeFrom s t m) (path : Nat → Nat) (ell : Nat)
    (hv : 1 ≤ path 0) (hp : MatchesPrefix s path ell) :
    (ell : ℝ) ≤ (8/3 : ℝ)*path 0 + (8*m-1)/3 := by
  have hn := finite_edit_thue_upper s m hag path ell hv hp
  have hn' : 3*ell+1 ≤ 8*path 0+8*m := by omega
  have hr : (3 : ℝ)*ell+1 ≤ 8*path 0+8*m := by exact_mod_cast hn'
  linarith

theorem finite_edit_real_coefficient_optimal (s : Nat → Bool) (m : Nat)
    (hag : AgreeFrom s t m) (c C : ℝ) (hc : c < 8/3) :
    ∃ v ell, 1 ≤ v ∧ IsMaximumPrefix s v ell ∧ c*v+C < ell := by
  have hw : ∀ requested, ∃ v ell, requested ≤ v ∧
      (1 ≤ v ∧ HasPrefix s v ell) ∧ 8*v ≤ 3*ell+(8*m+1) := by
    intro requested
    obtain ⟨n, path, hr, hv, hp, _, _, hb⟩ :=
      finite_edit_thue_lower_above s m hag requested
    exact ⟨path 0, 8*2^n-3, hr, ⟨hv, path, rfl, hp⟩, by omega⟩
  obtain ⟨v, ell, ⟨hv, hp⟩, hlarge⟩ :=
    coefficient_from_late_witnesses _ (8*m+1) hw c C hc
  obtain ⟨maximum, hm, _⟩ := finite_edit_thue_maximum s m hag v hv
  have hle : (ell : ℝ) ≤ maximum := by exact_mod_cast hm.2 ell hp
  exact ⟨v, maximum, hv, hm, lt_of_lt_of_le hlarge hle⟩

theorem phase_real_bound (a : Nat) (path : Nat → Nat) (ell : Nat)
    (hv : 1 ≤ path 0) (hp : MatchesPrefix (PhaseShift.shift t a) path ell) :
    (ell : ℝ) ≤ (8/3 : ℝ)*path 0 + (5*a-1)/3 := by
  have hn := PhaseShift.thueMorse_shift_prefix_bound a path ell hv hp
  have hn' : 3*ell+1 ≤ 8*path 0+5*a := by omega
  have hr : (3 : ℝ)*ell+1 ≤ 8*path 0+5*a := by exact_mod_cast hn'
  linarith

theorem phase_maximum_exists (a v : Nat) (hv : 1 ≤ v) :
    ∃ ell, IsMaximumPrefix (PhaseShift.shift t a) v ell := by
  apply bounded_prefix_maximum _ v (8*v+5*a)
  intro ell ⟨path, hzero, hp⟩
  have hb := PhaseShift.thueMorse_shift_prefix_bound a path ell (by omega) hp
  omega

theorem phase_real_coefficient_optimal (a : Nat) (c C : ℝ) (hc : c < 8/3) :
    ∃ v ell, 1 ≤ v ∧ IsMaximumPrefix (PhaseShift.shift t a) v ell ∧
      c*v+C < ell := by
  have hw : ∀ requested, ∃ v ell, requested ≤ v ∧
      (1 ≤ v ∧ HasPrefix (PhaseShift.shift t a) v ell) ∧
      8*v ≤ 3*ell+(3*a+1) := by
    intro requested
    obtain ⟨n, hn⟩ := SharpCorollaries.exists_large_dyadic (requested+a+1)
    obtain ⟨path, hlo, hhi, hv, hp⟩ :=
      PhaseShift.thueMorse_shift_dyadic_family a n (by omega)
    refine ⟨path 0, 8*2^n-a-3, by omega, ⟨hv, path, rfl, hp⟩, ?_⟩
    omega
  obtain ⟨v, ell, ⟨hv, hp⟩, hlarge⟩ :=
    coefficient_from_late_witnesses _ (3*a+1) hw c C hc
  obtain ⟨maximum, hm⟩ := phase_maximum_exists a v hv
  have hle : (ell : ℝ) ≤ maximum := by exact_mod_cast hm.2 ell hp
  exact ⟨v, maximum, hv, hm, lt_of_lt_of_le hlarge hle⟩

/-- A naturally indexed binary population is an actual real-birthdate
population by assigning each vertex its natural index cast to the reals. -/
def binaryRealOfNat (E : LabelledGraph) (p : BinaryNatPopulation E) :
    BinaryRealPopulation Nat where
  edge := E
  birth := fun v => (v : ℝ)
  infinite := (BirthOrder.infiniteVertices_iff_not_finiteCover Nat).mpr whole_infinite
  sublevels := by
    intro r
    obtain ⟨n, hn⟩ := exists_nat_gt r
    refine ⟨List.range n, ?_⟩
    intro v hv
    apply List.mem_range.mpr
    have hlt : (v : ℝ) < n := lt_of_le_of_lt hv hn
    exact_mod_cast hlt
  chronological := by
    intro x y b he
    have hlt := p.2.1.1 x y ⟨b, he⟩
    exact_mod_cast hlt
  unique := p.1
  roots := by
    obtain ⟨xs, hxs⟩ := p.2.2.1
    refine ⟨xs, ?_⟩
    intro y hy
    exact hxs y (fun x ⟨b, he⟩ => hy x b he)
  children := p.2.1.2.2.1
  parents := by
    intro y hy b
    have hn : ¬ Root (ForgetLabels E) y := by
      intro hr
      apply hy
      intro x a he
      exact hr x ⟨a, he⟩
    exact p.2.2.2 y hn b

/-- Unconditional binary classification in the literal real-birthdate model.
The universal quantifier here ranges over arbitrary small vertex types. -/
theorem binary_real_classification (s : Nat → Bool) :
    (∀ (V : Type) (p : BinaryRealPopulation V),
      ∃ path : Nat → V, ∀ k, p.edge (path k) (path (k+1)) (s k)) ↔
      EventuallyPeriodic s := by
  constructor
  · intro hall
    have hm := hall Nat (binaryRealOfNat (Edge s) (edge_is_binaryNatPopulation s))
    obtain ⟨path, hp⟩ := hm
    exact matching_implies_eventuallyPeriodic s path hp
  · intro hs V p
    exact eventuallyPeriodic_realized p s hs

/-- General finite-alphabet populations presented with actual real dates. -/
abbrev RealLabelledPopulation {V : Type u} (birth : V → ℝ) (k d : Nat) :=
  PopulationReindex.PresentedPopulation birth k d

theorem real_subcritical_impossible {V : Type u} {birth : V → ℝ} {k d : Nat}
    (p : RealLabelledPopulation birth k d) (hdk : d < k) : False :=
  PopulationReindex.subcritical_impossible p hdk

theorem real_at_least_k_distinct_roots {V : Type u} {birth : V → ℝ} {k d : Nat}
    (p : RealLabelledPopulation birth k d) :
    ∃ roots : Fin k → V, (∀ i, PopulationReindex.NoParents p.edge (roots i)) ∧
      ∀ i j, roots i = roots j → i = j :=
  PopulationReindex.at_least_k_distinct_roots p

theorem real_alphabet_le_root_cover_length
    {V : Type u} {birth : V → ℝ} {k d : Nat}
    (p : RealLabelledPopulation birth k d) (roots : List V)
    (hcover : ∀ x, PopulationReindex.NoParents p.edge x → x ∈ roots) :
    k ≤ roots.length :=
  PopulationReindex.alphabet_le_root_cover_length p roots hcover

end RealBridges
