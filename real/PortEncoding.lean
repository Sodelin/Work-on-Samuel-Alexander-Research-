import SamuelAlexanderResearch.PortDynamics
import SamuelAlexanderResearch.InfiniteConservation
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Fin

/-!
An actual critical-degree population has a finite fair port presentation on a
tail. The ports are constructed from actual crossing edges, rather than given
as an additional population hypothesis.
-/

namespace PortEncoding
open PopulationCounting InfiniteConservation
open scoped BigOperators

noncomputable section
local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem sumBelow_eq_sum_fin (n : Nat) (f : Nat → Nat) :
    sumBelow n f = ∑ i : Fin n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sumBelow_succ, Fin.sum_univ_castSucc]
    simpa using congrArg (fun x => x + f n) ih

variable {k : Nat} (p : InfiniteLabeledPopulation k k)

/-- A regular tail, obtained below from degree conservation. -/
def Regular (base : Nat) : Prop :=
  ∀ v, base ≤ v → p.root v = false ∧ fullInDegree p v = k ∧ fullOutDegree p v = k

abbrev Incoming (b : Nat) := {u : Fin b // (p.edge u b).isSome = true}
abbrev Outgoing (b : Nat) :=
  {v : Fin (p.childSupport b) // (p.edge b v).isSome = true}

instance (b : Nat) : Fintype (Incoming p b) := by unfold Incoming; infer_instance
instance (b : Nat) : Fintype (Outgoing p b) := by unfold Outgoing; infer_instance

theorem incoming_card (b : Nat) : Fintype.card (Incoming p b) = fullInDegree p b := by
  unfold Incoming
  rw [Fintype.card_subtype, Finset.card_filter, fullInDegree,
    sumBelow_eq_sum_fin]
  rfl

theorem outgoing_card (b : Nat) : Fintype.card (Outgoing p b) = fullOutDegree p b := by
  unfold Outgoing
  rw [Fintype.card_subtype, Finset.card_filter, fullOutDegree,
    sumBelow_eq_sum_fin]
  rfl

def chosenParent (b : Nat) (hr : p.root b = false) (a : Fin k) : Nat :=
  Classical.choose (p.parent_of_label b hr a a.isLt)

theorem chosenParent_edge (b : Nat) (hr : p.root b = false) (a : Fin k) :
    p.edge (chosenParent p b hr a) b = some a.val :=
  Classical.choose_spec (p.parent_of_label b hr a a.isLt)

def parentMap (b : Nat) (hr : p.root b = false) (a : Fin k) : Incoming p b :=
  ⟨⟨chosenParent p b hr a,
    p.birth_order _ _ (by simp [chosenParent_edge])⟩, by simp [chosenParent_edge]⟩

theorem parentMap_edge (b : Nat) (hr : p.root b = false) (a : Fin k) :
    p.edge (parentMap p b hr a).val.val b = some a.val :=
  chosenParent_edge p b hr a

theorem parentMap_injective (b : Nat) (hr : p.root b = false) :
    Function.Injective (parentMap p b hr) := by
  intro a c h
  have he := congrArg (fun x : Incoming p b => p.edge x.val.val b) h
  rw [parentMap_edge, parentMap_edge] at he
  exact Fin.ext (Option.some.inj he)

def parentEquiv (b : Nat) (hr : p.root b = false) (hi : fullInDegree p b = k) :
    Fin k ≃ Incoming p b :=
  Equiv.ofBijective (parentMap p b hr)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨parentMap_injective p b hr, by simp [incoming_card, hi]⟩)

@[simp] theorem parentEquiv_apply (b : Nat) (hr : p.root b = false)
    (hi : fullInDegree p b = k) (a : Fin k) :
    parentEquiv p b hr hi a = parentMap p b hr a := rfl

/-- Exact incoming degree and coverage rule out extra labels, even on edges
whose source precedes the chosen base. -/
theorem incoming_label_lt (b : Nat) (hr : p.root b = false)
    (hi : fullInDegree p b = k) (u label : Nat) (he : p.edge u b = some label) :
    label < k := by
  have hb : u < b := p.birth_order u b (by simp [he])
  let x : Incoming p b := ⟨⟨u, hb⟩, by simp [he]⟩
  obtain ⟨a, ha⟩ := (parentEquiv p b hr hi).surjective x
  have hlabel := parentMap_edge p b hr a
  have hu : (parentMap p b hr a).val.val = u :=
    congrArg (fun z : Incoming p b => z.val.val) ha
  rw [hu, he] at hlabel
  have : label = a.val := Option.some.inj hlabel
  exact this.symm ▸ a.isLt

def birthEquiv (b : Nat) (hr : p.root b = false)
    (hi : fullInDegree p b = k) (ho : fullOutDegree p b = k) :
    Incoming p b ≃ Outgoing p b :=
  (parentEquiv p b hr hi).symm.trans
    (Fintype.equivFinOfCardEq (by simpa [outgoing_card] using ho)).symm

/-- Actual edges crossing the cut immediately before birth `b`. -/
abbrev Cut (b : Nat) :=
  {e : Nat × Nat // e.1 < b ∧ b ≤ e.2 ∧ (p.edge e.1 e.2).isSome = true}

theorem target_lt_support {u v : Nat} (he : (p.edge u v).isSome = true) :
    v < p.childSupport u := by
  by_contra h
  have := p.no_children_after u v (Nat.le_of_not_gt h)
  simp [this] at he

def cutKey (b : Nat) (x : Cut p b) : Fin b × Fin (ambientBound p b) :=
  (⟨x.val.1, x.property.1⟩,
    ⟨x.val.2, Nat.lt_of_lt_of_le (target_lt_support p x.property.2.2)
      (support_le_ambient p b x.val.1 x.property.1)⟩)

theorem cutKey_injective (b : Nat) : Function.Injective (cutKey p b) := by
  intro x y h
  apply Subtype.ext
  exact Prod.ext (congrArg (fun z : Fin b × Fin (ambientBound p b) => z.1.val) h)
    (congrArg (fun z : Fin b × Fin (ambientBound p b) => z.2.val) h)

instance (b : Nat) : Finite (Cut p b) := Finite.of_injective _ (cutKey_injective p b)
instance (b : Nat) : Fintype (Cut p b) := Fintype.ofFinite _

def cutOfIncoming (b : Nat) (x : Incoming p b) : Cut p b :=
  ⟨(x.val.val, b), x.val.isLt, Nat.le_refl b, x.property⟩

def cutOfOutgoing (b : Nat) (x : Outgoing p b) : Cut p (b+1) :=
  ⟨(b, x.val.val), by omega,
    p.birth_order _ _ x.property, x.property⟩

def asIncoming (b : Nat) (x : Cut p b) (h : x.val.2 = b) : Incoming p b :=
  ⟨⟨x.val.1, x.property.1⟩, by simpa [h] using x.property.2.2⟩

def asOutgoing (b : Nat) (x : Cut p (b+1)) (h : x.val.1 = b) : Outgoing p b :=
  ⟨⟨x.val.2, target_lt_support p (by simpa [h] using x.property.2.2)⟩,
    by simpa [h] using x.property.2.2⟩

@[simp] theorem asIncoming_cut (b : Nat) (x : Incoming p b) (h) :
    asIncoming p b (cutOfIncoming p b x) h = x := by
  apply Subtype.ext
  apply Fin.ext
  rfl

@[simp] theorem asOutgoing_cut (b : Nat) (x : Outgoing p b) (h) :
    asOutgoing p b (cutOfOutgoing p b x) h = x := by
  apply Subtype.ext
  apply Fin.ext
  rfl

@[simp] theorem cut_asIncoming (b : Nat) (x : Cut p b) (h : x.val.2 = b) :
    cutOfIncoming p b (asIncoming p b x h) = x := by
  apply Subtype.ext
  exact Prod.ext rfl h.symm

@[simp] theorem cut_asOutgoing (b : Nat) (x : Cut p (b+1)) (h : x.val.1 = b) :
    cutOfOutgoing p b (asOutgoing p b x h) = x := by
  apply Subtype.ext
  exact Prod.ext h.symm rfl

def advance (b : Nat) (e : Incoming p b ≃ Outgoing p b) (x : Cut p b) : Cut p (b+1) :=
  if h : x.val.2 = b then cutOfOutgoing p b (e (asIncoming p b x h))
  else ⟨x.val, by have := x.property.1; omega,
    by have := x.property.2.1; omega, x.property.2.2⟩

def retreat (b : Nat) (e : Incoming p b ≃ Outgoing p b) (x : Cut p (b+1)) : Cut p b :=
  if h : x.val.1 = b then cutOfIncoming p b (e.symm (asOutgoing p b x h))
  else ⟨x.val, by have := x.property.1; omega,
    by have := x.property.2.1; omega, x.property.2.2⟩

@[simp] theorem advance_incoming (b : Nat) (e : Incoming p b ≃ Outgoing p b)
    (x : Incoming p b) :
    advance p b e (cutOfIncoming p b x) = cutOfOutgoing p b (e x) := by
  unfold advance
  rw [dif_pos (show (cutOfIncoming p b x).val.2 = b from rfl), asIncoming_cut]

@[simp] theorem retreat_outgoing (b : Nat) (e : Incoming p b ≃ Outgoing p b)
    (x : Outgoing p b) :
    retreat p b e (cutOfOutgoing p b x) = cutOfIncoming p b (e.symm x) := by
  unfold retreat
  rw [dif_pos (show (cutOfOutgoing p b x).val.1 = b from rfl), asOutgoing_cut]

theorem advance_survives (b : Nat) (e : Incoming p b ≃ Outgoing p b)
    (x : Cut p b) (h : x.val.2 ≠ b) : (advance p b e x).val = x.val := by
  simp [advance, h]

theorem retreat_survives (b : Nat) (e : Incoming p b ≃ Outgoing p b)
    (x : Cut p (b+1)) (h : x.val.1 ≠ b) : (retreat p b e x).val = x.val := by
  simp [retreat, h]

theorem retreat_advance (b : Nat) (e : Incoming p b ≃ Outgoing p b) (x : Cut p b) :
    retreat p b e (advance p b e x) = x := by
  by_cases h : x.val.2 = b
  · conv_rhs => rw [← cut_asIncoming p b x h]
    rw [advance, dif_pos h, retreat_outgoing, Equiv.symm_apply_apply]
  · have hv := advance_survives p b e x h
    have hn : (advance p b e x).val.1 ≠ b := by
      rw [hv]
      have := x.property.1
      omega
    apply Subtype.ext
    rw [retreat_survives p b e _ hn, hv]

theorem advance_retreat (b : Nat) (e : Incoming p b ≃ Outgoing p b)
    (x : Cut p (b+1)) : advance p b e (retreat p b e x) = x := by
  by_cases h : x.val.1 = b
  · conv_rhs => rw [← cut_asOutgoing p b x h]
    rw [retreat, dif_pos h, advance_incoming, Equiv.apply_symm_apply]
  · have hv := retreat_survives p b e x h
    have hn : (retreat p b e x).val.2 ≠ b := by
      rw [hv]
      have := x.property.2.1
      omega
    apply Subtype.ext
    rw [advance_survives p b e _ hn, hv]

/-- A birth permutes the finite crossing-edge slots: incoming edges are
replaced by outgoing edges, and every surviving edge keeps its slot. -/
def cutStep (b : Nat) (e : Incoming p b ≃ Outgoing p b) : Cut p b ≃ Cut p (b+1) where
  toFun := advance p b e
  invFun := retreat p b e
  left_inv := retreat_advance p b e
  right_inv := advance_retreat p b e

def incomingAt (base : Nat) (hr : Regular p base) (n : Nat) :
    Fin k ≃ Incoming p (base+n) :=
  parentEquiv p (base+n) (hr _ (by omega)).1 (hr _ (by omega)).2.1

def stepAt (base : Nat) (hr : Regular p base) (n : Nat) :
    Incoming p (base+n) ≃ Outgoing p (base+n) :=
  birthEquiv p (base+n) (hr _ (by omega)).1
    (hr _ (by omega)).2.1 (hr _ (by omega)).2.2

/-- Every state is a bijection from the original finite slots onto the actual
current crossing edges. -/
def states (base : Nat) (hr : Regular p base) :
    (n : Nat) → Fin (Fintype.card (Cut p base)) ≃ Cut p (base+n)
  | 0 => (Fintype.equivFin (Cut p base)).symm
  | n+1 => (states base hr n).trans (cutStep p (base+n) (stepAt p base hr n))

theorem states_succ (base : Nat) (hr : Regular p base) (n : Nat)
    (i : Fin (Fintype.card (Cut p base))) :
    states p base hr (n+1) i =
      advance p (base+n) (stepAt p base hr n) (states p base hr n i) := rfl

theorem cut_width_constant (base : Nat) (hr : Regular p base) (n : Nat) :
    Fintype.card (Cut p (base+n)) = Fintype.card (Cut p base) := by
  simpa only [Fintype.card_fin] using (Fintype.card_congr (states p base hr n)).symm

theorem tail_label_lt (base : Nat) (hr : Regular p base) (u v label : Nat)
    (hv : base ≤ v) (he : p.edge u v = some label) : label < k :=
  incoming_label_lt p v (hr v hv).1 (hr v hv).2.1 u label he

theorem cut_has_label {base b : Nat} (hr : Regular p base) (hb : base ≤ b)
    (x : Cut p b) : ∃ a : Fin k, p.edge x.val.1 x.val.2 = some a.val := by
  cases he : p.edge x.val.1 x.val.2 with
  | none => have hx := x.property.2.2; simp [he] at hx
  | some label =>
    exact ⟨⟨label, tail_label_lt p base hr _ _ label
      (Nat.le_trans hb x.property.2.1) he⟩, rfl⟩

def cutLabel {base b : Nat} (hr : Regular p base) (hb : base ≤ b)
    (x : Cut p b) : Fin k := Classical.choose (cut_has_label p hr hb x)

theorem cutLabel_edge {base b : Nat} (hr : Regular p base) (hb : base ≤ b)
    (x : Cut p b) : p.edge x.val.1 x.val.2 = some (cutLabel p hr hb x).val :=
  Classical.choose_spec (cut_has_label p hr hb x)

theorem cutLabel_congr {base b c : Nat} (hr : Regular p base)
    (hb : base ≤ b) (hc : base ≤ c) (x : Cut p b) (y : Cut p c)
    (h : x.val = y.val) : cutLabel p hr hb x = cutLabel p hr hc y := by
  have he := cutLabel_edge p hr hb x
  rw [h, cutLabel_edge p hr hc y] at he
  exact Fin.ext (Option.some.inj he).symm

def storedToken {base b : Nat} (hr : Regular p base) (hb : base ≤ b)
    (x : Cut p b) : PortDynamics.Token (Fin k) :=
  ⟨x.val.1, cutLabel p hr hb x⟩

theorem storedToken_congr {base b c : Nat} (hr : Regular p base)
    (hb : base ≤ b) (hc : base ≤ c) (x : Cut p b) (y : Cut p c)
    (h : x.val = y.val) : storedToken p hr hb x = storedToken p hr hc y := by
  have hs := congrArg Prod.fst h
  have hl := cutLabel_congr p hr hb hc x y h
  change PortDynamics.Token.mk _ _ = PortDynamics.Token.mk _ _
  rw [hs, hl]

def schedule (base : Nat) (hr : Regular p base) :
    PortDynamics.Schedule (Fintype.card (Cut p base)) (Fin k) where
  selected n i := (states p base hr n i).val.2 = base+n
  newLabel n i := cutLabel p hr (by omega) (states p base hr (n+1) i)

def initial (base : Nat) (hr : Regular p base) :
    Fin (Fintype.card (Cut p base)) → PortDynamics.Token (Fin k) :=
  fun i => storedToken p hr (by omega) (states p base hr 0 i)

theorem states_consumed (base : Nat) (hr : Regular p base) (n : Nat)
    (i : Fin (Fintype.card (Cut p base))) (h : (schedule p base hr).selected n i) :
    (states p base hr (n+1) i).val.1 = base+n := by
  change (states p base hr n i).val.2 = base+n at h
  rw [states_succ]
  simp [advance, h, cutOfOutgoing]

theorem states_survive_step (base : Nat) (hr : Regular p base) (n : Nat)
    (i : Fin (Fintype.card (Cut p base))) (h : ¬(schedule p base hr).selected n i) :
    (states p base hr (n+1) i).val = (states p base hr n i).val :=
  advance_survives p (base+n) (stepAt p base hr n) (states p base hr n i) h

/-- The frozen decoder's run is the source/label projection of the actual
edge stored in each slot. -/
theorem run_eq_stored (base : Nat) (hr : Regular p base) (n : Nat)
    (i : Fin (Fintype.card (Cut p base))) :
    PortDynamics.run (schedule p base hr) base (initial p base hr) n i =
      storedToken p hr (by omega) (states p base hr n i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [PortDynamics.run]
    dsimp only
    by_cases h : (schedule p base hr).selected n i
    · rw [if_pos h]
      change PortDynamics.Token.mk _ _ = PortDynamics.Token.mk _ _
      rw [states_consumed p base hr n i h]
      rfl
    · rw [if_neg h, ih]
      exact storedToken_congr p hr _ _ _ _ (states_survive_step p base hr n i h).symm

def inputSlot (base : Nat) (hr : Regular p base) (n : Nat) (a : Fin k) :
    Fin (Fintype.card (Cut p base)) :=
  (states p base hr n).symm (cutOfIncoming p (base+n) (incomingAt p base hr n a))

theorem inputSlot_state (base : Nat) (hr : Regular p base) (n : Nat) (a : Fin k) :
    states p base hr n (inputSlot p base hr n a) =
      cutOfIncoming p (base+n) (incomingAt p base hr n a) := by
  exact (states p base hr n).apply_symm_apply _

theorem inputSlot_selected_iff (base : Nat) (hr : Regular p base) (n : Nat)
    (i : Fin (Fintype.card (Cut p base))) :
    (schedule p base hr).selected n i ↔ ∃ a, inputSlot p base hr n a = i := by
  constructor
  · intro h
    let x := asIncoming p (base+n) (states p base hr n i) h
    let a := (incomingAt p base hr n).symm x
    refine ⟨a, ?_⟩
    apply (states p base hr n).injective
    rw [inputSlot_state]
    have hx : incomingAt p base hr n a = x := (incomingAt p base hr n).apply_symm_apply x
    rw [hx]
    exact cut_asIncoming p (base+n) (states p base hr n i) h
  · rintro ⟨a, rfl⟩
    change (states p base hr n (inputSlot p base hr n a)).val.2 = base+n
    rw [inputSlot_state]
    rfl

theorem inputSlot_label (base : Nat) (hr : Regular p base) (n : Nat) (a : Fin k) :
    (PortDynamics.run (schedule p base hr) base (initial p base hr) n
      (inputSlot p base hr n a)).label = a := by
  rw [run_eq_stored]
  change cutLabel p hr (by omega) (states p base hr n (inputSlot p base hr n a)) = a
  have he := cutLabel_edge p hr (show base ≤ base+n by omega)
    (states p base hr n (inputSlot p base hr n a))
  have hparent := parentMap_edge p (base+n) (hr _ (by omega)).1 a
  have hs : p.edge (states p base hr n (inputSlot p base hr n a)).val.1
      (states p base hr n (inputSlot p base hr n a)).val.2 = some a.val := by
    rw [inputSlot_state]
    exact hparent
  rw [hs] at he
  exact Fin.ext (Option.some.inj he).symm

def encoding_legal (base : Nat) (hr : Regular p base) :
    PortDynamics.Legal (schedule p base hr) base (initial p base hr) where
  old i := (states p base hr 0 i).property.1
  simple := by
    intro n i j hi hj hs
    rw [run_eq_stored, run_eq_stored] at hs
    apply (states p base hr n).injective
    apply Subtype.ext
    exact Prod.ext hs (hi.trans hj.symm)
  inputs := inputSlot p base hr
  selected_iff := inputSlot_selected_iff p base hr
  incoming_label := inputSlot_label p base hr

theorem states_survive (base : Nat) (hr : Regular p base) (n m : Nat)
    (i : Fin (Fintype.card (Cut p base))) (hnm : n ≤ m)
    (quiet : ∀ t, n ≤ t → t < m → ¬(schedule p base hr).selected t i) :
    (states p base hr m i).val = (states p base hr n i).val := by
  induction m with
  | zero =>
    have hn : n = 0 := by omega
    subst n
    rfl
  | succ m ih =>
    by_cases hnm' : n ≤ m
    · rw [states_survive_step p base hr m i (quiet m hnm' (by omega))]
      exact ih hnm' (fun t ht htm => quiet t ht (by omega))
    · have hn : n = m+1 := by omega
      subst n
      rfl

/-- A slot is consumed by the finite target time of its current actual edge. -/
theorem encoding_fair (base : Nat) (hr : Regular p base) :
    PortDynamics.Fair (schedule p base hr) := by
  intro n i
  let m := (states p base hr n i).val.2 - base
  have htarget := (states p base hr n i).property.2.1
  have hm : n ≤ m := by dsimp [m]; omega
  by_contra h
  have quiet : ∀ t, n ≤ t → t < m → ¬(schedule p base hr).selected t i := by
    intro t hnt _ ht
    exact h ⟨t, hnt, ht⟩
  have he := states_survive p base hr n m i hm quiet
  have hs : (schedule p base hr).selected m i := by
    change (states p base hr m i).val.2 = base+m
    rw [he]
    dsimp [m]
    omega
  exact h ⟨m, hm, hs⟩

/-- Every decoded edge is the actual stored edge consumed at its target. -/
theorem decoded_actual (base : Nat) (hr : Regular p base) (u v : Nat) (a : Fin k)
    (hd : PortDynamics.DecodedEdge (schedule p base hr) base (initial p base hr) u v a) :
    p.edge u v = some a.val := by
  obtain ⟨n, i, hv, hselected, hsource, hlabel⟩ := hd
  rw [run_eq_stored] at hsource hlabel
  have he := cutLabel_edge p hr (show base ≤ base+n by omega) (states p base hr n i)
  change (states p base hr n i).val.1 = u at hsource
  change cutLabel p hr (by omega) (states p base hr n i) = a at hlabel
  change (states p base hr n i).val.2 = base+n at hselected
  rw [hlabel, hsource, hselected, ← hv] at he
  exact he

/-- All actual edges targeting the tail, including initial crossings, decode. -/
theorem actual_decoded (base : Nat) (hr : Regular p base) (u v : Nat) (a : Fin k)
    (hv : base ≤ v) (he : p.edge u v = some a.val) :
    PortDynamics.DecodedEdge (schedule p base hr) base (initial p base hr) u v a := by
  let n := v-base
  have hvn : v = base+n := by dsimp [n]; omega
  have huv : u < v := p.birth_order u v (by simp [he])
  let x : Cut p (base+n) :=
    ⟨(u,v), by omega, by omega, by simp [he]⟩
  let i := (states p base hr n).symm x
  have hi : states p base hr n i = x := (states p base hr n).apply_symm_apply x
  refine ⟨n, i, hvn, ?_, ?_, ?_⟩
  · change (states p base hr n i).val.2 = base+n
    rw [hi]
    exact hvn
  · rw [run_eq_stored, hi]
    rfl
  · rw [run_eq_stored]
    change cutLabel p hr (by omega) (states p base hr n i) = a
    have hl := cutLabel_edge p hr (show base ≤ base+n by omega) (states p base hr n i)
    have he' : p.edge (states p base hr n i).val.1 (states p base hr n i).val.2 =
        some a.val := by rw [hi]; exact he
    rw [he'] at hl
    exact Fin.ext (Option.some.inj hl).symm

theorem encoding_exact (base : Nat) (hr : Regular p base) (u v : Nat) (a : Fin k)
    (hv : base ≤ v) :
    p.edge u v = some a.val ↔
      PortDynamics.DecodedEdge (schedule p base hr) base (initial p base hr) u v a :=
  ⟨actual_decoded p base hr u v a hv, decoded_actual p base hr u v a⟩

/-- Periodicity is a separate, explicit hypothesis. Under it, the existing
finite-port theorem transports its strict paths into the actual population. -/
theorem encoded_periodic_realizes (base : Nat) (hr : Regular p base)
    {M period : Nat} (hp : 0 < period)
    (hperiod : PortDynamics.PeriodicAfter (schedule p base hr) M period)
    (s : Nat → Fin k) :
    ∃ path : Nat → Nat, base+M ≤ path 0 ∧ path 0 < base+M+period ∧
      ∀ n, path n < path (n+1) ∧ p.edge (path n) (path (n+1)) = some (s n).val := by
  obtain ⟨path, hlo, hhi, hedge⟩ :=
    (encoding_legal p base hr).periodic_realizes hp hperiod s
  exact ⟨path, hlo, hhi, fun n =>
    ⟨(hedge n).1, decoded_actual p base hr _ _ _ (hedge n).2⟩⟩

/-- The actual-population encoder. All construction hypotheses are derived
from the original critical population; no port presentation is supplied. -/
theorem eventual_encoding :
    ∃ base C, ∃ S : PortDynamics.Schedule C (Fin k),
      ∃ init : Fin C → PortDynamics.Token (Fin k),
      p.rootSupport ≤ base ∧ C = Fintype.card (Cut p base) ∧
      Nonempty (PortDynamics.Legal S base init) ∧ PortDynamics.Fair S ∧
      (∀ u v (a : Fin k), base ≤ v →
        (p.edge u v = some a.val ↔ PortDynamics.DecodedEdge S base init u v a)) ∧
      (∀ u v label, base ≤ v → p.edge u v = some label → label < k) := by
  obtain ⟨base, hroot, hr, _⟩ := eventual_structure p
  exact ⟨base, Fintype.card (Cut p base), schedule p base hr, initial p base hr,
    hroot, rfl, ⟨encoding_legal p base hr⟩, encoding_fair p base hr,
    encoding_exact p base hr, tail_label_lt p base hr⟩

end
end PortEncoding

#print axioms PortEncoding.eventual_encoding
#print axioms PortEncoding.encoding_exact
#print axioms PortEncoding.encoding_fair
#print axioms PortEncoding.encoded_periodic_realizes
