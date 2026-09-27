import PairingCore

/-!
An exact static sampling criterion in PairingCore.Family.
The observed bit is co-ownership of two already labelled genome copies.
Neither sequence equality nor phasing alone supplies these ownership labels.
Infinite-record identifiability is distinct from a finite-time decision.
-/

namespace PairingObservation

open SpeciesBridge PairingCore

/-- Exact specimen co-ownership, not equality of DNA letters. -/
def query (K : Schedule) (t : Nat) : Bool :=
  decide (owner K (copy t 0) = owner K (copy t 3))

theorem query_coownership (K : Schedule) (t : Nat) :
    query K t = true ↔ owner K (copy t 0) = owner K (copy t 3) := by
  simp [query]

theorem local_query : ∀ k : Fin 3, block k 0 = block k 3 ↔ k = 2 := by decide

theorem query_formula (K : Schedule) (t : Nat) :
    query K t = decide (K t = 2) := by
  simp only [query, owner_copy, org_eq_iff, org_gen, org_idx, true_and, local_query]

theorem query_mixing (t : Nat) : query mixing t = false := by
  rw [query_formula]
  by_cases he : t % 2 = 0 <;> simp [mixing, he]

theorem query_splitting (S t : Nat) :
    query (splitting S) t = decide (S < t ∧ t % 2 = 1) := by
  rw [query_formula]
  by_cases hs : t ≤ S
  · have hn : ¬ S < t := by omega
    by_cases he : t % 2 = 0 <;> simp [splitting, mixing, hs, he, hn]
  · have hst : S < t := by omega
    by_cases he : t % 2 = 0
    · simp [splitting, hs, he, hst]
    · have ho : t % 2 = 1 := by omega
      simp [splitting, hs, hst, ho]

/-- T is a fixed, known sampling mask; missing data is not a negative answer. -/
noncomputable def observe (T : Nat → Prop) (K : Schedule) (t : Nat) : Option Bool := by
  classical
  exact if T t then some (query K t) else none

theorem observe_eq_iff (T : Nat → Prop) (K L : Schedule) :
    observe T K = observe T L ↔ ∀ t, T t → query K t = query L t := by
  classical
  constructor
  · intro h t ht
    have he := congrArg (fun f => f t) h
    simpa [observe, ht] using he
  · intro h
    funext t
    by_cases ht : T t <;> simp [observe, ht, h t]

theorem split_observation_eq_iff (T : Nat → Prop) (S : Nat) :
    observe T (splitting S) = observe T mixing ↔
      ∀ t, T t → ¬ (S < t ∧ t % 2 = 1) := by
  rw [observe_eq_iff]
  simp [query_splitting, query_mixing]

def UnboundedOdd (T : Nat → Prop) : Prop :=
  ∀ N, ∃ t, N < t ∧ T t ∧ t % 2 = 1

/-- A set-theoretic decoder of the whole infinite observation, not an algorithm. -/
def IdentifiesIAP (T : Nat → Prop) : Prop :=
  ∃ D : (Nat → Option Bool) → Prop, ∀ K, Family K →
    (D (observe T K) ↔ IAP (Edge K) Whole)

/-- The exact sampling criterion, restricted to the existing delayed-split family. -/
theorem identifies_iap_iff (T : Nat → Prop) : IdentifiesIAP T ↔ UnboundedOdd T := by
  classical
  constructor
  · rintro ⟨D, hD⟩ N
    apply Classical.byContradiction
    intro hn
    let S := 2 * (N + 1)
    have hS2 : 2 ≤ S := by dsimp [S]; omega
    have hSe : S % 2 = 0 := by dsimp [S]; omega
    have he : observe T (splitting S) = observe T mixing := by
      apply (split_observation_eq_iff T S).mpr
      intro t ht h
      exact hn ⟨t, by dsimp [S] at h; omega, ht, h.2⟩
    have hm := (hD mixing (Or.inl rfl)).mpr mixing_iap
    have hb := (hD (splitting S) (Or.inr ⟨S, hS2, hSe, rfl⟩)).mp
      (by rw [he]; exact hm)
    exact splitting_not_iap S hSe hb
  · intro hT
    refine ⟨fun obs => ∀ t, obs t ≠ some true, ?_⟩
    intro K hK
    rcases hK with rfl | ⟨S, hS2, hSe, rfl⟩
    · constructor
      · intro _; exact mixing_iap
      · intro _ t
        by_cases ht : T t <;> simp [observe, ht, query_mixing]
    · constructor
      · intro h
        obtain ⟨t, hst, ht, ho⟩ := hT S
        exact False.elim (h t (by simp [observe, ht, query_splitting, hst, ho]))
      · intro h
        exact False.elim (splitting_not_iap S hSe h)

theorem no_bounded_sampling_decoder (T : Nat → Prop) (N : Nat)
    (hT : ∀ t, T t → t ≤ N) : ¬ IdentifiesIAP T := by
  intro h
  obtain ⟨t, hnt, ht, _⟩ := (identifies_iap_iff T).mp h N
  have := hT t ht
  omega

/-- A positive observed bit already certifies the negative-IAP branch in Family. -/
theorem observed_positive_not_iap (T : Nat → Prop) (K : Schedule) (hK : Family K)
    (t : Nat) (ht : observe T K t = some true) : ¬ IAP (Edge K) Whole := by
  classical
  rcases hK with rfl | ⟨S, _, hSe, rfl⟩
  · by_cases hT : T t <;> simp [observe, hT, query_mixing] at ht
  · exact splitting_not_iap S hSe

/-- Even the entire owner assignment agrees at every even generation. -/
theorem even_owner_agreement (S g : Nat) (he : (g / 8) % 2 = 0) :
    owner (splitting S) g = owner mixing g := by
  by_cases hs : g / 8 ≤ S <;> simp [owner, splitting, mixing, hs, he]

def evenOwners (K : Schedule) (g : Nat) : Option Nat :=
  if (g / 8) % 2 = 0 then some (owner K g) else none

theorem even_owners_equal (S : Nat) : evenOwners (splitting S) = evenOwners mixing := by
  funext g
  by_cases he : (g / 8) % 2 = 0
  · simp [evenOwners, he, even_owner_agreement S g he]
  · simp [evenOwners, he]

/-- Unlimited even-generation ownership, plus the whole copy graph, still fails. -/
theorem no_even_ownership_decoder :
    ¬ ∃ D : Graph → (Nat → Option Nat) → Prop, ∀ K, Family K →
      (D Genome (evenOwners K) ↔ IAP (Edge K) Whole) := by
  rintro ⟨D, hD⟩
  have hm := (hD mixing (Or.inl rfl)).mpr mixing_iap
  have hb := (hD (splitting 2) (Or.inr ⟨2, by decide, by decide, rfl⟩)).mp
    (by rw [even_owners_equal]; exact hm)
  exact splitting_not_iap 2 (by decide) hb

/-- Additional prior knowledge: any permanent switch must occur by B. -/
def BoundedFamily (B : Nat) (K : Schedule) : Prop :=
  K = mixing ∨ ∃ S, 2 ≤ S ∧ S % 2 = 0 ∧ S ≤ B ∧ K = splitting S

def BoundedIdentifiesIAP (T : Nat → Prop) (B : Nat) : Prop :=
  ∃ D : (Nat → Option Bool) → Prop, ∀ K, BoundedFamily B K →
    (D (observe T K) ↔ IAP (Edge K) Whole)

/-- A sharp finite-data boundary within the explicitly bounded model class. -/
theorem bounded_identifies_iap_iff (T : Nat → Prop) (B : Nat)
    (hB2 : 2 ≤ B) (hBe : B % 2 = 0) :
    BoundedIdentifiesIAP T B ↔ ∃ t, B < t ∧ T t ∧ t % 2 = 1 := by
  classical
  constructor
  · rintro ⟨D, hD⟩
    apply Classical.byContradiction
    intro hn
    have he : observe T (splitting B) = observe T mixing := by
      apply (split_observation_eq_iff T B).mpr
      intro t ht h
      exact hn ⟨t, h.1, ht, h.2⟩
    have hm := (hD mixing (Or.inl rfl)).mpr mixing_iap
    have hb := (hD (splitting B) (Or.inr ⟨B, hB2, hBe, by omega, rfl⟩)).mp
      (by rw [he]; exact hm)
    exact splitting_not_iap B hBe hb
  · rintro ⟨t, hbt, ht, ho⟩
    refine ⟨fun obs => obs t = some false, ?_⟩
    intro K hK
    rcases hK with rfl | ⟨S, _, hSe, hSB, rfl⟩
    · constructor
      · intro _; exact mixing_iap
      · intro _; simp [observe, ht, query_mixing]
    · have hst : S < t := by omega
      constructor
      · intro h
        simp [observe, ht, query_splitting, hst, ho] at h
      · intro h
        exact False.elim (splitting_not_iap S hSe h)

/-- One exact query suffices only after supplying the restrictive switch bound. -/
theorem bounded_iap_iff_one_query (B : Nat) (hBe : B % 2 = 0)
    (K : Schedule) (hK : BoundedFamily B K) :
    IAP (Edge K) Whole ↔ query K (B + 1) = false := by
  rcases hK with rfl | ⟨S, _, hSe, hSB, rfl⟩
  · constructor
    · intro _; exact query_mixing _
    · intro _; exact mixing_iap
  · have hst : S < B + 1 := by omega
    have ho : (B + 1) % 2 = 1 := by omega
    constructor
    · intro h; exact False.elim (splitting_not_iap S hSe h)
    · intro h
      simp [query_splitting, hst, ho] at h

end PairingObservation
