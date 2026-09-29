import WongWaitingTimes
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Finset.Powerset

set_option autoImplicit false

/-! Independent spatial innovations for the stopped Big-ARG process.

The array is indexed by event number AND the finite active-lineage set. Thus
the selected identities have their exact uniform law without relying on an
arbitrary enumeration of the frontier. Empty and singleton inactive indices
are explicit totalizations. The cut law in this module is continuous uniform
on (0,L); a discrete internal-link law is a different specialization.

The product marginal theorem alone is not a graph-process theorem. The
recorder/count invariant and its almost-sure valid fold must also be supplied.
-/
namespace WongMarkedLaw
open MeasureTheory ProbabilityTheory WongCountChain WongWaitingTimes
open scoped ENNReal NNReal BigOperators Classical
noncomputable section

def LegalStep (k l : ℕ) : Prop :=
  if k ≤ 1 then l = 1 else l = k + 1 ∨ l + 1 = k

theorem transition_ae_legal (θ : ℝ≥0) (k : ℕ) :
    ∀ᵐ l ∂jumpKernel θ k, LegalStep k l := by
  rw [ae_iff]
  rcases k with _ | (_ | j)
  · simp [jumpKernel, transition, LegalStep]
  · simp [jumpKernel, transition, LegalStep]
  · have hj : ¬j + 2 ≤ 1 := by omega
    simp [jumpKernel, transition, LegalStep, hj]

/-- Legal adjacent steps under the actual Ionescu--Tulcea path law. This uses
the joint prefix/next-state law, not merely single-time marginal equalities. -/
theorem path_ae_legal (θ : ℝ≥0) (n : ℕ) :
    ∀ᵐ K ∂pathLaw θ n, ∀ t, LegalStep (K t) (K (t + 1)) := by
  rw [ae_all_iff]
  intro t
  let ν := Kernel.partialTraj (X := fun _ => ℕ) (historyKernel θ) 0 t (fun _ => n)
  have hj : ν ⊗ₘ historyKernel θ t =
      (pathLaw θ n).map (fun K => (Preorder.frestrictLe t K, K (t + 1))) :=
    Kernel.partialTraj_compProd_eq_map_traj (X := fun _ : ℕ => ℕ)
      (κ := historyKernel θ) (Nat.zero_le t)
  have hs : ∀ᵐ z ∂(ν ⊗ₘ historyKernel θ t),
      LegalStep (z.1 ⟨t, Finset.mem_Iic.mpr le_rfl⟩) z.2 := by
    apply Measure.ae_compProd_of_ae_ae
    · exact (Set.to_countable _).measurableSet
    · exact Filter.Eventually.of_forall (fun h =>
        transition_ae_legal θ (h ⟨t, Finset.mem_Iic.mpr le_rfl⟩))
  rw [hj] at hs
  exact ae_of_ae_map (by fun_prop) hs

/-- The finite choice law is uniform on a nonempty set. The empty-set value
is a disclosed totalization, never a valid pre-absorption lineage choice. -/
def finiteChoiceLaw {α : Type*} [MeasurableSpace α] [Inhabited α]
    (s : Finset α) : Measure α :=
  if h : s.Nonempty then (PMF.uniformOfFinset s h).toMeasure else Measure.dirac default

instance finiteChoiceLaw_probability {α : Type*} [MeasurableSpace α] [Inhabited α]
    (s : Finset α) : IsProbabilityMeasure (finiteChoiceLaw s) := by
  unfold finiteChoiceLaw
  split <;> infer_instance

theorem finiteChoiceLaw_singleton {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Inhabited α] (s : Finset α)
    (hs : s.Nonempty) (x : α) :
    finiteChoiceLaw s {x} = if x ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0 := by
  rw [finiteChoiceLaw, dif_pos hs, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton x)]
  exact PMF.uniformOfFinset_apply hs x

theorem finiteChoiceLaw_ae_mem {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Inhabited α] (s : Finset α)
    (hs : s.Nonempty) : ∀ᵐ x ∂finiteChoiceLaw s, x ∈ s := by
  rw [ae_iff, finiteChoiceLaw, dif_pos hs]
  rw [PMF.toMeasure_uniformOfFinset_apply hs {x | x ∉ s}
    (s.finite_toSet.measurableSet.compl)]
  simp

def cutLaw (L : ℝ) (_hL : 0 < L) : Measure ℝ :=
  ProbabilityTheory.cond volume (Set.Ioo 0 L)

instance cutLaw_probability (L : ℝ) (hL : 0 < L) :
    IsProbabilityMeasure (cutLaw L hL) := by
  apply cond_isProbabilityMeasure_of_finite
  · simpa [Real.volume_Ioo] using hL
  · simp [Real.volume_Ioo]

theorem cutLaw_ae_interior (L : ℝ) (hL : 0 < L) :
    ∀ᵐ x ∂cutLaw L hL, 0 < x ∧ x < L :=
  ae_cond_mem measurableSet_Ioo

theorem cutLaw_apply (L : ℝ) (hL : 0 < L) (B : Set ℝ)
    (hB : MeasurableSet B) :
    cutLaw L hL B = volume (Set.Ioo 0 L ∩ B) / ENNReal.ofReal L := by
  rw [cutLaw, cond_apply' hB]
  simp [Real.volume_Ioo, ENNReal.div_eq_inv_mul]

abbrev SpatialMark := ℕ × (Finset ℕ × ℝ)
abbrev InnovationIndex := ℕ × Finset ℕ
abbrev Innovations := InnovationIndex → SpatialMark
abbrev Sample := WongWaitingTimes.Sample × Innovations

/-- Independent lineage, unordered-pair, and breakpoint innovations. Only the
choice appropriate to the count jump is used by the recorder. -/
def markLaw (L : ℝ) (hL : 0 < L) (s : Finset ℕ) : Measure SpatialMark :=
  (finiteChoiceLaw s).prod ((finiteChoiceLaw (s.powersetCard 2)).prod (cutLaw L hL))

instance markLaw_probability (L : ℝ) (hL : 0 < L) (s : Finset ℕ) :
    IsProbabilityMeasure (markLaw L hL s) := by unfold markLaw; infer_instance

theorem mark_lineage_marginal (L : ℝ) (hL : 0 < L) (s : Finset ℕ) :
    (markLaw L hL s).map Prod.fst = finiteChoiceLaw s := by
  exact (measurePreserving_fst (μ := finiteChoiceLaw s)
    (ν := (finiteChoiceLaw (s.powersetCard 2)).prod (cutLaw L hL))).map_eq

theorem mark_pair_cut_marginal (L : ℝ) (hL : 0 < L) (s : Finset ℕ) :
    (markLaw L hL s).map Prod.snd =
      (finiteChoiceLaw (s.powersetCard 2)).prod (cutLaw L hL) := by
  exact (measurePreserving_snd (μ := finiteChoiceLaw s)
    (ν := (finiteChoiceLaw (s.powersetCard 2)).prod (cutLaw L hL))).map_eq

theorem mark_pair_marginal (L : ℝ) (hL : 0 < L) (s : Finset ℕ) :
    (markLaw L hL s).map (fun m => m.2.1) = finiteChoiceLaw (s.powersetCard 2) := by
  change (markLaw L hL s).map
    ((Prod.fst : Finset ℕ × ℝ → Finset ℕ) ∘ (Prod.snd : SpatialMark → Finset ℕ × ℝ)) = _
  rw [← Measure.map_map measurable_fst measurable_snd, mark_pair_cut_marginal]
  exact (measurePreserving_fst (μ := finiteChoiceLaw (s.powersetCard 2))
    (ν := cutLaw L hL)).map_eq

theorem mark_cut_marginal (L : ℝ) (hL : 0 < L) (s : Finset ℕ) :
    (markLaw L hL s).map (fun m => m.2.2) = cutLaw L hL := by
  change (markLaw L hL s).map
    ((Prod.snd : Finset ℕ × ℝ → ℝ) ∘ (Prod.snd : SpatialMark → Finset ℕ × ℝ)) = _
  rw [← Measure.map_map measurable_snd measurable_snd, mark_pair_cut_marginal]
  exact (measurePreserving_snd (μ := finiteChoiceLaw (s.powersetCard 2))
    (ν := cutLaw L hL)).map_eq

theorem unordered_pair_mass (s p : Finset ℕ) (hs : 2 ≤ s.card)
    (hp : p ⊆ s ∧ p.card = 2) :
    finiteChoiceLaw (s.powersetCard 2) {p} = (s.card.choose 2 : ℝ≥0∞)⁻¹ := by
  rw [finiteChoiceLaw_singleton _ (Finset.powersetCard_nonempty.mpr hs)]
  simp [Finset.mem_powersetCard.mpr hp, Finset.card_powersetCard]

def ValidSpatialMark (L : ℝ) (s : Finset ℕ) (m : SpatialMark) : Prop :=
  (s.Nonempty → m.1 ∈ s) ∧
  (2 ≤ s.card → m.2.1 ⊆ s ∧ m.2.1.card = 2) ∧ 0 < m.2.2 ∧ m.2.2 < L

theorem markLaw_ae_valid (L : ℝ) (hL : 0 < L) (s : Finset ℕ) :
    ∀ᵐ m ∂markLaw L hL s, ValidSpatialMark L s m := by
  have hl : ∀ᵐ m ∂markLaw L hL s, s.Nonempty → m.1 ∈ s := by
    by_cases hs : s.Nonempty
    · have h := ae_of_ae_map (μ := markLaw L hL s) measurable_fst.aemeasurable (by
        rw [mark_lineage_marginal]
        exact finiteChoiceLaw_ae_mem s hs)
      filter_upwards [h] with m hm using fun _ => hm
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hs h))
  have hp : ∀ᵐ m ∂markLaw L hL s,
      2 ≤ s.card → m.2.1 ⊆ s ∧ m.2.1.card = 2 := by
    by_cases hs : 2 ≤ s.card
    · have h := ae_of_ae_map (μ := markLaw L hL s)
        (f := fun m : SpatialMark => m.2.1)
        (p := fun p : Finset ℕ => p ∈ s.powersetCard 2)
        (measurable_fst.comp measurable_snd).aemeasurable (by
          rw [mark_pair_marginal]
          exact finiteChoiceLaw_ae_mem (s.powersetCard 2)
            (Finset.powersetCard_nonempty.mpr hs))
      filter_upwards [h] with m hm using fun _ => Finset.mem_powersetCard.mp hm
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hs h))
  have hc : ∀ᵐ m ∂markLaw L hL s, 0 < m.2.2 ∧ m.2.2 < L :=
    ae_of_ae_map (μ := markLaw L hL s) (f := fun m : SpatialMark => m.2.2)
      (p := fun x : ℝ => 0 < x ∧ x < L)
      (measurable_snd.comp measurable_snd).aemeasurable (by
        rw [mark_cut_marginal]; exact cutLaw_ae_interior L hL)
  filter_upwards [hl, hp, hc] with m hl hp hc using ⟨hl, hp, hc⟩

def innovationLaw (L : ℝ) (hL : 0 < L) : Measure Innovations :=
  Measure.infinitePi (fun ix : InnovationIndex => markLaw L hL ix.2)

instance innovationLaw_probability (L : ℝ) (hL : 0 < L) :
    IsProbabilityMeasure (innovationLaw L hL) := by unfold innovationLaw; infer_instance

theorem innovation_marginal (L : ℝ) (hL : 0 < L) (ix : InnovationIndex) :
    (innovationLaw L hL).map (fun M => M ix) = markLaw L hL ix.2 :=
  Measure.infinitePi_map_eval _ ix

theorem innovations_independent (L : ℝ) (hL : 0 < L) :
    iIndepFun (fun ix (M : Innovations) => M ix) (innovationLaw L hL) :=
  iIndepFun_infinitePi (P := fun ix : InnovationIndex => markLaw L hL ix.2)
    (X := fun (_ : InnovationIndex) (m : SpatialMark) => m) (fun _ => measurable_id)

theorem innovations_ae_all_valid (L : ℝ) (hL : 0 < L) :
    ∀ᵐ M ∂innovationLaw L hL, ∀ ix, ValidSpatialMark L ix.2 (M ix) := by
  rw [ae_all_iff]
  intro ix
  exact ae_of_ae_map (μ := innovationLaw L hL) (measurable_pi_apply ix).aemeasurable (by
    rw [innovation_marginal]; exact markLaw_ae_valid L hL ix.2)

def law (L : ℝ) (hL : 0 < L) (θ : ℝ≥0) (n : ℕ) : Measure Sample :=
  (jointLaw θ n).prod (innovationLaw L hL)

instance law_probability (L : ℝ) (hL : 0 < L) (θ : ℝ≥0) (n : ℕ) :
    IsProbabilityMeasure (law L hL θ n) := by unfold law; infer_instance

/-- Exact whole-path count-and-clock marginal, including all their dependence. -/
theorem timed_count_marginal (L : ℝ) (hL : 0 < L) (θ : ℝ≥0) (n : ℕ) :
    (law L hL θ n).map Prod.fst = jointLaw θ n :=
  (measurePreserving_fst (μ := jointLaw θ n) (ν := innovationLaw L hL)).map_eq

theorem mark_array_marginal (L : ℝ) (hL : 0 < L) (θ : ℝ≥0) (n : ℕ) :
    (law L hL θ n).map Prod.snd = innovationLaw L hL :=
  (measurePreserving_snd (μ := jointLaw θ n) (ν := innovationLaw L hL)).map_eq

theorem timed_count_independent_marks (L : ℝ) (hL : 0 < L) (θ : ℝ≥0) (n : ℕ) :
    (fun z : Sample => z.1) ⟂ᵢ[law L hL θ n] (fun z : Sample => z.2) := by
  simpa only [law, id_eq] using
    (indepFun_prod (μ := jointLaw θ n) (ν := innovationLaw L hL)
      (X := id) (Y := id) measurable_id measurable_id)

theorem law_ae_all_marks_valid (L : ℝ) (hL : 0 < L) (θ : ℝ≥0) (n : ℕ) :
    ∀ᵐ z ∂law L hL θ n, ∀ ix, ValidSpatialMark L ix.2 (z.2 ix) :=
  ae_of_ae_map (μ := law L hL θ n) measurable_snd.aemeasurable (by
    rw [mark_array_marginal]; exact innovations_ae_all_valid L hL)

theorem law_ae_legal (L : ℝ) (hL : 0 < L) (θ : ℝ≥0) (n : ℕ) :
    ∀ᵐ z ∂law L hL θ n, ∀ t, LegalStep (z.1.1 t) (z.1.1 (t + 1)) := by
  apply ae_of_ae_map (μ := law L hL θ n)
    (p := fun z : WongWaitingTimes.Sample => ∀ t, LegalStep (z.1 t) (z.1 (t+1)))
    measurable_fst.aemeasurable
  rw [timed_count_marginal]
  apply ae_of_ae_map (μ := jointLaw θ n)
    (p := fun K : CountPath => ∀ t, LegalStep (K t) (K (t+1)))
    measurable_fst.aemeasurable
  rw [joint_count_marginal]
  exact path_ae_legal θ n

#print axioms path_ae_legal
#print axioms finiteChoiceLaw_singleton
#print axioms cutLaw_probability
#print axioms cutLaw_apply
#print axioms unordered_pair_mass
#print axioms markLaw_ae_valid
#print axioms innovations_independent
#print axioms innovations_ae_all_valid
#print axioms timed_count_marginal
#print axioms timed_count_independent_marks
#print axioms law_ae_all_marks_valid
#print axioms law_ae_legal
end
end WongMarkedLaw
