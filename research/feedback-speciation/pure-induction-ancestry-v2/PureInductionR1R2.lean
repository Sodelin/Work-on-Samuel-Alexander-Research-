import PureInductionJoint
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
R1/R2 working module. Imported PureInductionJoint is the preserved checked
finite4 source; this file alone owns new raw-fibre and all-marginal claims.
-/
namespace PureInductionR1R2
open PureInductionJoint
open scoped BigOperators

abbrev Slot := Fin 2 × Fin 2

def ticketParent (d : Fin 2) (t : Fin 14) : Fin 2 :=
  if t.val % 7 < 6 then d else other d

def slotGood (p : Table) (h : Homologues) (d s : Fin 2) (t : Fin 14) : Prop :=
  ticketParent d t = p d s ∧ t.val / 7 = (h d s).val

theorem slot_fibre_card (d parent hom : Fin 2) :
    ((Finset.univ : Finset (Fin 14)).filter
      (fun t => ticketParent d t = parent ∧ t.val / 7 = hom.val)).card =
      if parent = d then 6 else 1 := by
  fin_cases d <;> fin_cases parent <;> fin_cases hom <;> decide

def rawFibreEquiv (p : Table) (h : Homologues) :
    {u : RawNoise // rawParent u = p ∧ rawHomologue u = h} ≃
      (∀ d : Fin 2, ∀ s : Fin 2, {t : Fin 14 // slotGood p h d s t}) where
  toFun u d s := ⟨u.val d s, by
    rcases u.property with ⟨hp, hh⟩
    constructor
    · have he := congrFun (congrFun hp d) s
      simpa only [rawParent, ticketParent] using he
    · have he := congrArg Fin.val (congrFun (congrFun hh d) s)
      simpa only [rawHomologue] using he⟩
  invFun f := ⟨fun d s => (f d s).val, by
    constructor
    · funext d s
      exact (f d s).property.1
    · funext d s
      apply Fin.ext
      exact (f d s).property.2⟩
  left_inv := by
    intro u
    apply Subtype.ext
    funext d s
    rfl
  right_inv := by
    intro f
    funext d s
    apply Subtype.ext
    rfl

theorem raw_fibre_card (p : Table) (h : Homologues) :
    Fintype.card {u : RawNoise // rawParent u = p ∧ rawHomologue u = h} =
      tableWeight p := by
  classical
  calc
    Fintype.card {u : RawNoise // rawParent u = p ∧ rawHomologue u = h} =
        Fintype.card (∀ d : Fin 2, ∀ s : Fin 2,
          {t : Fin 14 // slotGood p h d s t}) :=
      Fintype.card_congr (rawFibreEquiv p h)
    _ = ∏ d : Fin 2, ∏ s : Fin 2,
          (if p d s = d then 6 else 1) := by
      simp only [Fintype.card_pi]
      apply Finset.prod_congr rfl
      intro d _
      apply Finset.prod_congr rfl
      intro s _
      rw [Fintype.card_subtype]
      have heq : ((Finset.univ : Finset (Fin 14)).filter (slotGood p h d s)) =
          ((Finset.univ : Finset (Fin 14)).filter
            (fun t => ticketParent d t = p d s ∧ t.val / 7 = (h d s).val)) := by
        apply Finset.filter_congr
        intro t _
        rfl
      rw [heq]
      exact slot_fibre_card d (p d s) (h d s)
    _ = tableWeight p := rfl

theorem raw_fibre_filter_card (p : Table) (h : Homologues) :
    ((Finset.univ : Finset RawNoise).filter
      (fun u => rawParent u = p ∧ rawHomologue u = h)).card =
      tableWeight p := by
  classical
  simpa only [Fintype.card_subtype] using raw_fibre_card p h

def project (u : RawNoise) : Table × Homologues :=
  (rawParent u, rawHomologue u)

/-- Transport every event on compressed parent/homologue records to its raw
Fin14^4 preimage. -/
theorem raw_event_card (E : Table × Homologues → Prop) [DecidablePred E] :
    ((Finset.univ : Finset RawNoise).filter (fun u => E (project u))).card =
      ∑ r : Table × Homologues, if E r then tableWeight r.1 else 0 := by
  classical
  let t : Finset (Table × Homologues) :=
    (Finset.univ : Finset (Table × Homologues)).filter E
  have hf := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset RawNoise) t project
  have hsum :
      (∑ r ∈ t, ((Finset.univ : Finset RawNoise).filter
        (fun u => project u = r)).card) =
      ∑ r ∈ t, tableWeight r.1 := by
    apply Finset.sum_congr rfl
    intro r hr
    rcases r with ⟨p, h⟩
    simpa only [project, Prod.mk.injEq] using raw_fibre_filter_card p h
  calc
    ((Finset.univ : Finset RawNoise).filter (fun u => E (project u))).card =
        ∑ r ∈ t, ((Finset.univ : Finset RawNoise).filter
          (fun u => project u = r)).card := by
      simpa only [t, Finset.mem_filter, Finset.mem_univ, true_and] using hf.symm
    _ = ∑ r ∈ t, tableWeight r.1 := hsum
    _ = ∑ r : Table × Homologues, if E r then tableWeight r.1 else 0 := by
      simp only [t, Finset.sum_filter]

theorem raw_ordinary_event_card (b : BState) (c : Nat × Nat) :
    ((Finset.univ : Finset RawNoise).filter
      (fun u => rawOrdinaryStep b u = c)).card =
      ordinaryNumerator b c := by
  have h := raw_event_card (fun r : Table × Homologues =>
    ordinaryStep b r.1 r.2 = c)
  convert h using 1
  · congr 1
  · rw [ordinaryNumerator, Fintype.sum_prod_type]

theorem raw_pulse_event_card (c : Nat × Nat) :
    ((Finset.univ : Finset RawNoise).filter
      (fun u => rawPulseInitStep u = c)).card =
      pulseNumerator c := by
  have h := raw_event_card (fun r : Table × Homologues =>
    pulseInitStep r.1 r.2 = c)
  convert h using 1
  · congr 1
  · rw [pulseNumerator, Fintype.sum_prod_type]

theorem raw_designated_numerator :
    ((Finset.univ : Finset RawNoise).filter
      (fun u => designated (rawParent u))).card = 576 := by
  have h := raw_event_card (fun r : Table × Homologues =>
    designated r.1 = true)
  have hsum : (∑ r : Table × Homologues,
      if designated r.1 = true then tableWeight r.1 else 0) =
      designatedNumerator := by
    rw [designatedNumerator, Fintype.sum_prod_type]
  have hp : ((Finset.univ : Finset RawNoise).filter
      (fun u => designated (rawParent u) = true)).card =
      designatedNumerator := by
    convert h.trans hsum using 1
    congr 1
  calc
    ((Finset.univ : Finset RawNoise).filter
      (fun u => designated (rawParent u))).card =
        ((Finset.univ : Finset RawNoise).filter
          (fun u => designated (rawParent u) = true)).card := by
      congr 1
    _ = designatedNumerator := hp
    _ = 576 := designated_numerator

theorem ordinary_marker_le (b : BState) (p : Table) (h : Homologues)
    (d s : Fin 2) : ordinaryMarker b p h d s ≤ 1 := by
  unfold ordinaryMarker
  split_ifs <;> omega

theorem pulse_marker_le (p : Table) (h : Homologues) (d s : Fin 2) :
    pulseMarker p h d s ≤ 1 := by
  unfold pulseMarker
  split_ifs
  · omega
  · exact ordinary_marker_le _ _ _ _ _

theorem raw_ordinary_step_lt (b : BState) (u : RawNoise) :
    (rawOrdinaryStep b u).1 < 3 ∧ (rawOrdinaryStep b u).2 < 3 := by
  have h00 := ordinary_marker_le b (rawParent u) (rawHomologue u) 0 0
  have h01 := ordinary_marker_le b (rawParent u) (rawHomologue u) 0 1
  have h10 := ordinary_marker_le b (rawParent u) (rawHomologue u) 1 0
  have h11 := ordinary_marker_le b (rawParent u) (rawHomologue u) 1 1
  dsimp [rawOrdinaryStep, ordinaryStep, pairCounts]
  omega

theorem raw_pulse_step_lt (u : RawNoise) :
    (rawPulseInitStep u).1 < 3 ∧ (rawPulseInitStep u).2 < 3 := by
  have h00 := pulse_marker_le (rawParent u) (rawHomologue u) 0 0
  have h01 := pulse_marker_le (rawParent u) (rawHomologue u) 0 1
  have h10 := pulse_marker_le (rawParent u) (rawHomologue u) 1 0
  have h11 := pulse_marker_le (rawParent u) (rawHomologue u) 1 1
  dsimp [rawPulseInitStep, pulseInitStep, pairCounts]
  omega

def ordinaryState (b : BState) (u : RawNoise) : BState :=
  (⟨(rawOrdinaryStep b u).1, (raw_ordinary_step_lt b u).1⟩,
   ⟨(rawOrdinaryStep b u).2, (raw_ordinary_step_lt b u).2⟩)

def pulseState (u : RawNoise) : BState :=
  (⟨(rawPulseInitStep u).1, (raw_pulse_step_lt u).1⟩,
   ⟨(rawPulseInitStep u).2, (raw_pulse_step_lt u).2⟩)

@[simp] theorem ordinaryState_vals (b : BState) (u : RawNoise) :
    ((ordinaryState b u).1.val, (ordinaryState b u).2.val) =
      rawOrdinaryStep b u := rfl

@[simp] theorem pulseState_vals (u : RawNoise) :
    ((pulseState u).1.val, (pulseState u).2.val) =
      rawPulseInitStep u := rfl


/-- All nine pure-B source states and nine pure-B destinations: 81 exact
cross-multiplied ordinary marginals. -/
theorem ordinary_all_cross (b c : BState) :
    ordinaryNumerator b (c.1.val, c.2.val) *
      FiniteEpigenetic.denominator (embed b).val =
    FiniteEpigenetic.numerator true false (embed b).val (embed c).val *
      38416 := by
  decide +kernel +revert

/-- The nine exact pulse initialization marginals. -/
theorem pulse_all_cross (c : BState) :
    pulseNumerator (c.1.val, c.2.val) *
      FiniteEpigenetic.denominator 54 =
    FiniteEpigenetic.numerator true true 54 (embed c).val *
      38416 := by
  decide +kernel +revert


/-- No ordinary raw probability is assigned to a frozen destination outside
the nine embedded pure-B states. -/
theorem ordinary_off_support (b : BState) (y : FiniteEpigenetic.State)
    (hy : ∀ c : BState, embed c ≠ y) :
    FiniteEpigenetic.numerator true false (embed b).val y.val = 0 := by
  decide +kernel +revert

/-- The one-time pulse likewise has only the nine pure-B destinations. -/
theorem pulse_off_support (y : FiniteEpigenetic.State)
    (hy : ∀ c : BState, embed c ≠ y) :
    FiniteEpigenetic.numerator true true 54 y.val = 0 := by
  decide +kernel +revert


theorem ordinary_denominator_pos (b : BState) :
    0 < FiniteEpigenetic.denominator (embed b).val := by
  decide +kernel +revert

/-- Every raw ordinary event probability agrees with the frozen kernel. -/
theorem ordinary_all_real (b c : BState) :
    (((Finset.univ : Finset RawNoise).filter
      (fun u => ordinaryState b u = c)).card : ℝ) / 38416 =
      (FiniteEpigenetic.kernel true).transition (embed b) (embed c) := by
  have he (u : RawNoise) :
      ordinaryState b u = c ↔
      rawOrdinaryStep b u = (c.1.val, c.2.val) := by
    constructor
    · intro h
      rw [← ordinaryState_vals b u, h]
    · intro h
      rw [← ordinaryState_vals b u] at h
      apply Prod.ext
      · apply Fin.ext
        exact congrArg Prod.fst h
      · apply Fin.ext
        exact congrArg Prod.snd h
  have hc : ((Finset.univ : Finset RawNoise).filter
      (fun u => ordinaryState b u = c)).card =
      ordinaryNumerator b (c.1.val, c.2.val) := by
    calc
      _ = ((Finset.univ : Finset RawNoise).filter
        (fun u => rawOrdinaryStep b u = (c.1.val, c.2.val))).card := by
          apply congrArg Finset.card
          apply Finset.filter_congr
          intro u _
          exact he u
      _ = _ := raw_ordinary_event_card b (c.1.val, c.2.val)
  rw [hc]
  change (ordinaryNumerator b (c.1.val, c.2.val) : ℝ) / 38416 =
    (FiniteEpigenetic.numerator true false (embed b).val (embed c).val : ℝ) /
      (FiniteEpigenetic.denominator (embed b).val : ℝ)
  have hd : (FiniteEpigenetic.denominator (embed b).val : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (ordinary_denominator_pos b))
  apply (div_eq_div_iff (by norm_num : (38416 : ℝ) ≠ 0) hd).2
  have h := congrArg (fun n : Nat => (n : ℝ)) (ordinary_all_cross b c)
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using h

/-- Every raw pulse probability agrees with frozen one-time initialization. -/
theorem pulse_all_real (c : BState) :
    (((Finset.univ : Finset RawNoise).filter
      (fun u => pulseState u = c)).card : ℝ) / 38416 =
      FiniteEpigenetic.pulse true (embed c) := by
  have he (u : RawNoise) :
      pulseState u = c ↔
      rawPulseInitStep u = (c.1.val, c.2.val) := by
    constructor
    · intro h
      rw [← pulseState_vals u, h]
    · intro h
      rw [← pulseState_vals u] at h
      apply Prod.ext
      · apply Fin.ext
        exact congrArg Prod.fst h
      · apply Fin.ext
        exact congrArg Prod.snd h
  have hc : ((Finset.univ : Finset RawNoise).filter
      (fun u => pulseState u = c)).card =
      pulseNumerator (c.1.val, c.2.val) := by
    calc
      _ = ((Finset.univ : Finset RawNoise).filter
        (fun u => rawPulseInitStep u = (c.1.val, c.2.val))).card := by
          apply congrArg Finset.card
          apply Finset.filter_congr
          intro u _
          exact he u
      _ = _ := raw_pulse_event_card (c.1.val, c.2.val)
  rw [hc]
  change (pulseNumerator (c.1.val, c.2.val) : ℝ) / 38416 =
    (FiniteEpigenetic.numerator true true 54 (embed c).val : ℝ) /
      (FiniteEpigenetic.denominator 54 : ℝ)
  have hden : 0 < FiniteEpigenetic.denominator 54 := by decide +kernel
  have hd : (FiniteEpigenetic.denominator 54 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hden)
  apply (div_eq_div_iff (by norm_num : (38416 : ℝ) ≠ 0) hd).2
  have h := congrArg (fun n : Nat => (n : ℝ)) (pulse_all_cross c)
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using h

theorem ordinary_off_support_real (b : BState) (y : FiniteEpigenetic.State)
    (hy : ∀ c : BState, embed c ≠ y) :
    (FiniteEpigenetic.kernel true).transition (embed b) y = 0 := by
  change (FiniteEpigenetic.numerator true false (embed b).val y.val : ℝ) /
    (FiniteEpigenetic.denominator (embed b).val : ℝ) = 0
  rw [ordinary_off_support b y hy]
  norm_num

theorem pulse_off_support_real (y : FiniteEpigenetic.State)
    (hy : ∀ c : BState, embed c ≠ y) :
    FiniteEpigenetic.pulse true y = 0 := by
  change (FiniteEpigenetic.numerator true true 54 y.val : ℝ) /
    (FiniteEpigenetic.denominator 54 : ℝ) = 0
  rw [pulse_off_support y hy]
  norm_num

end PureInductionR1R2

#print axioms PureInductionR1R2.raw_fibre_card
#print axioms PureInductionR1R2.raw_event_card
#print axioms PureInductionR1R2.raw_designated_numerator
#print axioms PureInductionR1R2.ordinaryState_vals
#print axioms PureInductionR1R2.ordinary_all_cross
#print axioms PureInductionR1R2.pulse_all_cross
#print axioms PureInductionR1R2.ordinary_off_support
#print axioms PureInductionR1R2.pulse_off_support
#print axioms PureInductionR1R2.ordinary_all_real
#print axioms PureInductionR1R2.pulse_all_real
