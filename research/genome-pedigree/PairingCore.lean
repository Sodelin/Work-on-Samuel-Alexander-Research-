import SamuelAlexanderResearch.SpeciesGlobalIAP

/-!
Unknown ownership in a complete realised genome-copy transmission graph.
Eight persistent lanes admit connected, nonselfing diploid pedigrees with
opposite whole-population IAP. No probability or biological identification
claim is made. `Shared` is exactly the edge image, not a sound overapproximation.
-/

namespace PairingCore

open SpeciesBridge SpeciesGlobalIAP

def block (k : Fin 3) (l : Fin 8) : Fin 4 :=
  if k = 0 then
    match l.val with
    | 0 | 1 => 0
    | 2 | 3 => 1
    | 4 | 5 => 2
    | _ => 3
  else if k = 1 then
    match l.val with
    | 1 | 2 => 0
    | 3 | 4 => 1
    | 5 | 6 => 2
    | _ => 3
  else
    match l.val with
    | 1 | 2 => 0
    | 3 | 0 => 1
    | 5 | 6 => 2
    | _ => 3

def Shared (a b : Fin 3) (i j : Fin 4) : Prop :=
  ∃ l : Fin 8, block a l = i ∧ block b l = j

instance (a b : Fin 3) (i j : Fin 4) : Decidable (Shared a b i j) :=
  inferInstanceAs (Decidable (∃ l : Fin 8, block a l = i ∧ block b l = j))

def org (t : Nat) (i : Fin 4) : Nat := 4 * t + i.val
def idx (n : Nat) : Fin 4 := ⟨n % 4, Nat.mod_lt _ (by decide)⟩
def copy (t : Nat) (l : Fin 8) : Nat := 8 * t + l.val
def lane (n : Nat) : Fin 8 := ⟨n % 8, Nat.mod_lt _ (by decide)⟩

@[simp] theorem org_gen (t : Nat) (i : Fin 4) : org t i / 4 = t := by
  have := i.isLt
  unfold org
  omega

@[simp] theorem org_idx (t : Nat) (i : Fin 4) : idx (org t i) = i := by
  apply Fin.ext
  have := i.isLt
  simp only [idx, org]
  omega

@[simp] theorem org_decode (n : Nat) : org (n / 4) (idx n) = n := by
  simp only [org, idx]
  omega

@[simp] theorem copy_gen (t : Nat) (l : Fin 8) : copy t l / 8 = t := by
  have := l.isLt
  unfold copy
  omega

@[simp] theorem copy_lane (t : Nat) (l : Fin 8) : lane (copy t l) = l := by
  apply Fin.ext
  have := l.isLt
  simp only [lane, copy]
  omega

@[simp] theorem copy_decode (n : Nat) : copy (n / 8) (lane n) = n := by
  simp only [copy, lane]
  omega

abbrev Schedule := Nat → Fin 3

def owner (K : Schedule) (g : Nat) : Nat := org (g / 8) (block (K (g / 8)) (lane g))
def Genome : Graph := fun g h => h / 8 = g / 8 + 1 ∧ lane g = lane h
def Edge (K : Schedule) : Graph := fun u v =>
  v / 4 = u / 4 + 1 ∧ Shared (K (u / 4)) (K (v / 4)) (idx u) (idx v)

@[simp] theorem owner_copy (K : Schedule) (t : Nat) (l : Fin 8) :
    owner K (copy t l) = org t (block (K t) l) := by simp [owner]

@[simp] theorem edge_org (K : Schedule) (t s : Nat) (i j : Fin 4) :
    Edge K (org t i) (org s j) ↔ s = t + 1 ∧ Shared (K t) (K s) i j := by
  simp [Edge]

theorem edge_exact_image (K : Schedule) (u v : Nat) :
    Edge K u v ↔ ∃ g h, Genome g h ∧ owner K g = u ∧ owner K h = v := by
  constructor
  · rintro ⟨ht, l, hu, hv⟩
    refine ⟨copy (u / 4) l, copy (v / 4) l, ?_, ?_, ?_⟩
    · simpa [Genome] using And.intro ht (rfl : l = l)
    · simp [hu]
    · simp [hv]
  · rintro ⟨g, h, ht, rfl, rfl⟩
    simp only [owner, edge_org]
    exact ⟨ht.1, lane g, rfl, by rw [ht.2]⟩

theorem block_two : ∀ (k : Fin 3) (i : Fin 4), ∃ a b : Fin 8,
    a ≠ b ∧ ∀ l, block k l = i ↔ l = a ∨ l = b := by decide

theorem owner_exactly_two (K : Schedule) (v : Nat) : ∃ a b : Nat,
    a ≠ b ∧ ∀ g, owner K g = v ↔ g = a ∨ g = b := by
  obtain ⟨a, b, hab, hp⟩ := block_two (K (v / 4)) (idx v)
  refine ⟨copy (v / 4) a, copy (v / 4) b, ?_, ?_⟩
  · intro h
    have := congrArg lane h
    exact hab (by simpa using this)
  · intro g
    constructor
    · intro h
      have ht := congrArg (fun n => n / 4) h
      have hi := congrArg idx h
      simp only [owner, org_gen, org_idx] at ht hi
      rw [ht] at hi
      rcases (hp (lane g)).mp hi with ha | hb
      · left; calc
          g = copy (g/8) (lane g) := (copy_decode g).symm
          _ = copy (v/4) a := by rw [ht, ha]
      · right; calc
          g = copy (g/8) (lane g) := (copy_decode g).symm
          _ = copy (v/4) b := by rw [ht, hb]
    · rintro (rfl | rfl) <;> simp [((hp a).mpr (Or.inl rfl)), ((hp b).mpr (Or.inr rfl))]

def mixing (t : Nat) : Fin 3 := if t % 2 = 0 then 0 else 1
def splitting (S t : Nat) : Fin 3 := if t ≤ S then mixing t else if t % 2 = 0 then 0 else 2

theorem mixing_step (t : Nat) :
    (mixing t = 0 ∧ mixing (t+1) = 1 ∧ mixing (t+2) = 0 ∧ mixing (t+3) = 1) ∨
    (mixing t = 1 ∧ mixing (t+1) = 0 ∧ mixing (t+2) = 1 ∧ mixing (t+3) = 0) := by
  by_cases ht : t % 2 = 0
  · left; simp [mixing, ht, show (t+1)%2 ≠ 0 by omega,
      show (t+2)%2 = 0 by omega, show (t+3)%2 ≠ 0 by omega]
  · right; simp [mixing, ht, show (t+1)%2 = 0 by omega,
      show (t+3)%2 = 0 by omega]

theorem local_mixing : ∀ (a b : Fin 3), (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) →
    ∀ i j : Fin 4, ∃ p q : Fin 4,
      Shared a b i p ∧ Shared b a p q ∧ Shared a b q j := by decide

theorem local_diagonal : ∀ (a b : Fin 3),
    ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0)) →
    ∀ i : Fin 4, Shared a b i i := by decide

theorem mixing_three (t : Nat) (i j : Fin 4) :
    Descendant (Edge mixing) (org t i) (org (t+3) j) := by
  rcases mixing_step t with h | h
  all_goals
    obtain ⟨p, q, hp, hq, hj⟩ := local_mixing (mixing t) (mixing (t+1))
      (by simp only [h.1, h.2.1]; decide) i j
    have h1 : Edge mixing (org t i) (org (t+1) p) := (edge_org ..).mpr ⟨rfl, hp⟩
    have h2 : Edge mixing (org (t+1) p) (org (t+2) q) := by
      apply (edge_org ..).mpr
      refine ⟨by omega, ?_⟩
      simpa only [h.1, h.2.1, h.2.2.1] using hq
    have h3 : Edge mixing (org (t+2) q) (org (t+3) j) := by
      apply (edge_org ..).mpr
      refine ⟨by omega, ?_⟩
      simpa only [h.1, h.2.1, h.2.2.1, h.2.2.2] using hj
    exact ((Descendant.edge h1).snoc h2).snoc h3

theorem mixing_diagonal (t : Nat) (i : Fin 4) :
    Edge mixing (org t i) (org (t+1) i) := by
  apply (edge_org ..).mpr
  refine ⟨rfl, local_diagonal _ _ ?_ i⟩
  rcases mixing_step t with h | h
  · exact Or.inl ⟨h.1, h.2.1⟩
  · exact Or.inr (Or.inl ⟨h.1, h.2.1⟩)

theorem mixing_late (t s : Nat) (i j : Fin 4) (h : t+3 ≤ s) :
    Descendant (Edge mixing) (org t i) (org s j) := by
  induction s with
  | zero => omega
  | succ s ih =>
    by_cases he : s+1 = t+3
    · rw [he]; exact mixing_three t i j
    · exact (ih (by omega)).snoc (mixing_diagonal s j)

theorem mixing_cofinite : CofiniteDescendants (Edge mixing) := by
  intro u
  apply (finiteSupport_iff_bounded _).mpr
  refine ⟨4 * (u/4+3), ?_⟩
  intro v hn
  have hg : v/4 < u/4+3 := by
    by_cases h : v/4 < u/4+3
    · exact h
    · apply False.elim
      apply hn
      have := mixing_late (u/4) (v/4) (idx u) (idx v) (by omega)
      simpa using this
  omega

theorem mixing_iap : IAP (Edge mixing) Whole :=
  (iap_whole_iff _).mpr (fun u => Or.inr (mixing_cofinite u))

theorem mixing_inspecies : Inspecies (Edge mixing) Whole :=
  (whole_inspecies_iff_cofinite_descendants _).mpr mixing_cofinite

theorem mixing_connected : WeaklyConnected (Edge mixing) Whole := by
  refine ⟨⟨0, trivial⟩, ?_⟩
  intro u v _ _
  have hu := mixing_late (u/4) (u/4+v/4+3) (idx u) 0 (by omega)
  have hv := mixing_late (v/4) (u/4+v/4+3) (idx v) 0 (by omega)
  simp only [org_decode] at hu hv
  exact hu.weakReach_whole.trans hv.weakReach_whole.symm

theorem mixing_specieslike : Specieslike (Edge mixing) Whole :=
  ⟨mixing_connected, mixing_iap, whole_convex _⟩

theorem mixing_maximal : MaximalSpecieslike (Edge mixing) Whole :=
  ⟨mixing_specieslike, fun _ _ _ _ _ => trivial⟩

def Allowed (a b : Fin 3) : Prop :=
  (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0)

instance (a b : Fin 3) : Decidable (Allowed a b) := by unfold Allowed; infer_instance

theorem splitting_tail (S t : Nat) (hS : S % 2 = 0) (ht : S ≤ t) :
    splitting S t = if t % 2 = 0 then 0 else 2 := by
  by_cases h : t ≤ S
  · have he : t = S := by omega
    subst t
    simp [splitting, mixing, hS]
  · simp [splitting, h]

theorem splitting_step (S t : Nat) (hS : S % 2 = 0) :
    Allowed (splitting S t) (splitting S (t+1)) := by
  by_cases ht : t < S
  · have h1 : t ≤ S := by omega
    have h2 : t+1 ≤ S := by omega
    simp only [splitting, if_pos h1, if_pos h2]
    rcases mixing_step t with h | h
    · exact Or.inl ⟨h.1, h.2.1⟩
    · exact Or.inr (Or.inl ⟨h.1, h.2.1⟩)
  · rw [splitting_tail S t hS (by omega), splitting_tail S (t+1) hS (by omega)]
    by_cases hp : t % 2 = 0
    · have hq : (t+1)%2 ≠ 0 := by omega
      simp [Allowed, hp, hq]
    · have hq : (t+1)%2 = 0 := by omega
      simp [Allowed, hp, hq]

theorem splitting_diagonal (S t : Nat) (hS : S % 2 = 0) (i : Fin 4) :
    Edge (splitting S) (org t i) (org (t+1) i) :=
  (edge_org ..).mpr ⟨rfl, local_diagonal _ _ (splitting_step S t hS) i⟩

theorem local_halves : ∀ a b : Fin 3, (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0) →
    ∀ i j : Fin 4, Shared a b i j ↔ i.val / 2 = j.val / 2 := by decide

theorem splitting_tail_edge (S t : Nat) (hS : S % 2 = 0) (ht : S ≤ t) (i j : Fin 4) :
    Edge (splitting S) (org t i) (org (t+1) j) ↔ i.val/2 = j.val/2 := by
  rw [edge_org]
  simp only [true_and]
  apply local_halves
  rw [splitting_tail S t hS ht, splitting_tail S (t+1) hS (by omega)]
  by_cases hp : t % 2 = 0
  · simp [hp, show (t+1)%2 ≠ 0 by omega]
  · simp [hp, show (t+1)%2 = 0 by omega]

theorem descendant_time {K : Schedule} {u v : Nat} (h : Descendant (Edge K) u v) :
    u/4 < v/4 := by
  induction h with
  | edge h => have := h.1; omega
  | snoc _ h ih => have := h.1; omega

theorem tail_invariant (S : Nat) (hS : S%2=0) {u v : Nat}
    (hu : S ≤ u/4) (h : Descendant (Edge (splitting S)) u v) :
    (idx u).val/2 = (idx v).val/2 := by
  induction h with
  | @edge v h =>
    have hh : Edge (splitting S) (org (u/4) (idx u)) (org (u/4+1) (idx v)) := by
      rw [← h.1]; simpa using h
    exact (splitting_tail_edge S (u/4) hS hu _ _).mp hh
  | @snoc v w huv hvw ih =>
    have hv : S ≤ v/4 := by have := descendant_time huv; omega
    have hh : Edge (splitting S) (org (v/4) (idx v)) (org (v/4+1) (idx w)) := by
      rw [← hvw.1]; simpa using hvw
    exact ih.trans ((splitting_tail_edge S (v/4) hS hv _ _).mp hh)

theorem tail_reaches (S t s : Nat) (hS : S%2=0) (ht : S ≤ t)
    (i j : Fin 4) (hij : i.val/2 = j.val/2) (h : t < s) :
    Descendant (Edge (splitting S)) (org t i) (org s j) := by
  induction s with
  | zero => omega
  | succ s ih =>
    by_cases he : s = t
    · subst s
      exact .edge ((splitting_tail_edge S t hS ht i j).mpr hij)
    · exact (ih (by omega)).snoc (splitting_diagonal S s hS j)

theorem split_infinite_descendants (S : Nat) (hS : S%2=0) :
    InfiniteSupport (Descendant (Edge (splitting S)) (org S 0)) := by
  intro hfin
  obtain ⟨b, hb⟩ := (finiteSupport_iff_bounded _).mp hfin
  have hr := tail_reaches S S (S+b+1) hS (by omega) 0 0 rfl (by omega)
  have := hb _ hr
  simp only [org, Fin.val_zero] at this
  omega

theorem split_infinite_nondescendants (S : Nat) (hS : S%2=0) :
    InfiniteSupport (fun v => ¬ Descendant (Edge (splitting S)) (org S 0) v) := by
  intro hfin
  obtain ⟨b, hb⟩ := (finiteSupport_iff_bounded _).mp hfin
  have hn : ¬ Descendant (Edge (splitting S)) (org S 0) (org (S+b+1) 2) := by
    intro h
    have hi := tail_invariant S hS (by simp) h
    simp at hi
  have := hb _ hn
  simp only [org] at this
  omega

theorem splitting_not_iap (S : Nat) (hS : S%2=0) : ¬ IAP (Edge (splitting S)) Whole := by
  intro hiap
  rcases (iap_whole_iff _).mp hiap (org S 0) with hd | hn
  · exact split_infinite_descendants S hS hd
  · exact split_infinite_nondescendants S hS hn

theorem splitting_not_inspecies (S : Nat) (hS : S%2=0) :
    ¬ Inspecies (Edge (splitting S)) Whole := by
  intro h
  exact split_infinite_nondescendants S hS ((whole_inspecies_iff_cofinite_descendants _).mp h _)

theorem splitting_not_specieslike (S : Nat) (hS : S%2=0) :
    ¬ Specieslike (Edge (splitting S)) Whole := fun h => splitting_not_iap S hS h.2.1

theorem prefix_owner_agreement (S g : Nat) (hg : g/8 ≤ S) :
    owner (splitting S) g = owner mixing g := by
  simp [owner, splitting, hg]

theorem arbitrary_prefix_opposite_iap (N : Nat) : ∃ S : Nat,
    (∀ g, g/8 ≤ N → owner (splitting S) g = owner mixing g) ∧
    IAP (Edge mixing) Whole ∧ ¬ IAP (Edge (splitting S)) Whole := by
  refine ⟨2*(N+1), ?_, mixing_iap, splitting_not_iap _ (by omega)⟩
  intro g hg
  exact prefix_owner_agreement _ g (by omega)

theorem local_connected : ∀ i j : Fin 4, ∃ p q r : Fin 4,
    Shared 0 1 i p ∧ Shared 0 1 q p ∧ Shared 0 1 q r ∧ Shared 0 1 j r := by decide

theorem connected_of_prefix (K : Schedule) (h0 : K 0 = 0) (h1 : K 1 = 1)
    (hd : ∀ t i, Edge K (org t i) (org (t+1) i)) : WeaklyConnected (Edge K) Whole := by
  have origin : ∀ t i, WeakReach (Edge K) Whole (org 0 i) (org t i) := by
    intro t i
    induction t with
    | zero => exact .refl trivial
    | succ t ih => exact ih.trans (.edge trivial trivial (Or.inl (hd t i)))
  have roots : ∀ i j, WeakReach (Edge K) Whole (org 0 i) (org 0 j) := by
    intro i j
    obtain ⟨p, q, r, hp, hq, hr, hj⟩ := local_connected i j
    have he : ∀ a b, Shared 0 1 a b → Edge K (org 0 a) (org 1 b) := by
      intro a b h
      apply (edge_org ..).mpr
      exact ⟨rfl, by simpa [h0, h1] using h⟩
    exact (WeakReach.edge trivial trivial (Or.inl (he i p hp))).trans
      ((WeakReach.edge trivial trivial (Or.inr (he q p hq))).trans
        ((WeakReach.edge trivial trivial (Or.inl (he q r hr))).trans
          (WeakReach.edge trivial trivial (Or.inr (he j r hj)))))
  refine ⟨⟨0, trivial⟩, ?_⟩
  intro u v _ _
  have h := (origin (u/4) (idx u)).symm.trans
    ((roots (idx u) (idx v)).trans (origin (v/4) (idx v)))
  simpa using h

theorem splitting_connected (S : Nat) (hS : S%2=0) (hS2 : 2 ≤ S) :
    WeaklyConnected (Edge (splitting S)) Whole :=
  connected_of_prefix _ (by simp [splitting, mixing])
    (by simp [splitting, mixing, show 1 ≤ S by omega]) (splitting_diagonal S · hS)

theorem local_two_children : ∀ a b : Fin 3, Allowed a b → ∀ i : Fin 4,
    ∃ j k : Fin 4, j ≠ k ∧ ∀ l, Shared a b i l ↔ l = j ∨ l = k := by decide

theorem local_two_parents : ∀ a b : Fin 3, Allowed a b → ∀ j : Fin 4,
    ∃ i k : Fin 4, i ≠ k ∧ ∀ l, Shared a b l j ↔ l = i ∨ l = k := by decide

theorem local_opposite_sex : ∀ a b : Fin 3, Allowed a b → ∀ i j k : Fin 4,
    Shared a b i k → Shared a b j k → i ≠ j → i.val%2 ≠ j.val%2 := by decide

theorem org_eq_iff (v t : Nat) (i : Fin 4) : v = org t i ↔ v/4 = t ∧ idx v = i := by
  constructor
  · rintro rfl; simp
  · rintro ⟨ht, hi⟩
    calc
      v = org (v/4) (idx v) := (org_decode v).symm
      _ = org t i := by rw [ht, hi]

def TwoChildren (E : Graph) : Prop := ∀ u, ∃ a b : Nat,
  a ≠ b ∧ ∀ v, E u v ↔ v = a ∨ v = b
def TwoParents (E : Graph) : Prop := ∀ v, 0 < v/4 → ∃ a b : Nat,
  a ≠ b ∧ ∀ u, E u v ↔ u = a ∨ u = b

theorem two_children (K : Schedule) (hK : ∀ t, Allowed (K t) (K (t+1))) : TwoChildren (Edge K) := by
  intro u
  obtain ⟨a, b, hab, hp⟩ := local_two_children _ _ (hK (u/4)) (idx u)
  refine ⟨org (u/4+1) a, org (u/4+1) b, ?_, ?_⟩
  · intro h; exact hab (by simpa using congrArg idx h)
  · intro v
    constructor
    · rintro ⟨ht, hs⟩
      rw [ht] at hs
      rcases (hp (idx v)).mp hs with ha | hb
      · exact Or.inl ((org_eq_iff ..).mpr ⟨ht, ha⟩)
      · exact Or.inr ((org_eq_iff ..).mpr ⟨ht, hb⟩)
    · rintro (rfl | rfl) <;> simp only [Edge, org_gen, org_idx, true_and]
      · exact (hp a).mpr (Or.inl rfl)
      · exact (hp b).mpr (Or.inr rfl)

theorem two_parents (K : Schedule) (hK : ∀ t, Allowed (K t) (K (t+1))) : TwoParents (Edge K) := by
  intro v hv
  have ht : v/4-1+1 = v/4 := by omega
  obtain ⟨a, b, hab, hp⟩ := local_two_parents _ _ (hK (v/4-1)) (idx v)
  rw [ht] at hp
  refine ⟨org (v/4-1) a, org (v/4-1) b, ?_, ?_⟩
  · intro h; exact hab (by simpa using congrArg idx h)
  · intro u
    constructor
    · rintro ⟨hg, hs⟩
      have hg' : u/4 = v/4-1 := by omega
      rw [hg'] at hs
      rcases (hp (idx u)).mp hs with ha | hb
      · exact Or.inl ((org_eq_iff ..).mpr ⟨hg', ha⟩)
      · exact Or.inr ((org_eq_iff ..).mpr ⟨hg', hb⟩)
    · rintro (rfl | rfl) <;> simp only [Edge, org_gen, org_idx, ht, true_and]
      · exact (hp a).mpr (Or.inl rfl)
      · exact (hp b).mpr (Or.inr rfl)

theorem mixing_allowed (t : Nat) : Allowed (mixing t) (mixing (t+1)) := by
  rcases mixing_step t with h | h
  · exact Or.inl ⟨h.1, h.2.1⟩
  · exact Or.inr (Or.inl ⟨h.1, h.2.1⟩)

theorem pedigrees_two_children (S : Nat) (hS : S%2=0) :
    TwoChildren (Edge mixing) ∧ TwoChildren (Edge (splitting S)) :=
  ⟨two_children _ mixing_allowed, two_children _ (splitting_step S · hS)⟩

theorem pedigrees_two_parents (S : Nat) (hS : S%2=0) :
    TwoParents (Edge mixing) ∧ TwoParents (Edge (splitting S)) :=
  ⟨two_parents _ mixing_allowed, two_parents _ (splitting_step S · hS)⟩

theorem parents_opposite_sex (K : Schedule) (hK : ∀ t, Allowed (K t) (K (t+1)))
    (u v w : Nat) (hu : Edge K u w) (hv : Edge K v w) (hne : u ≠ v) :
    (idx u).val%2 ≠ (idx v).val%2 := by
  have ht : v/4 = u/4 := by have := hu.1; have := hv.1; omega
  have hi : idx u ≠ idx v := by
    intro h; apply hne
    calc
      u = org (u/4) (idx u) := (org_decode u).symm
      _ = org (v/4) (idx v) := by rw [h, ht]
      _ = v := org_decode v
  apply local_opposite_sex _ _ (hK (u/4)) (idx u) (idx v) (idx w) _ _ hi
  · simpa only [← hu.1] using hu.2
  · simpa only [← hu.1, ht] using hv.2

theorem genome_path_lane {g h : Nat} (hp : Descendant Genome g h) : lane g = lane h := by
  induction hp with
  | edge h => exact h.2
  | snoc _ h ih => exact ih.trans h.2

/-- Exact edge images do not reflect organism paths: the two edges use different copies. -/
theorem exact_edges_do_not_lift_paths : Descendant (Edge mixing) 0 9 ∧
    ¬ ∃ g h, owner mixing g = 0 ∧ owner mixing h = 9 ∧ Descendant Genome g h := by
  constructor
  · have h1 : Edge mixing 0 4 := by
      change 1=0+1 ∧ Shared 0 1 0 0
      decide
    have h2 : Edge mixing 4 9 := by
      change 2=1+1 ∧ Shared 1 0 0 1
      decide
    exact (Descendant.edge h1).snoc h2
  · rintro ⟨g, h, hg, hh, hp⟩
    have gt := congrArg (fun n => n/4) hg
    have ht := congrArg (fun n => n/4) hh
    simp only [owner, org_gen] at gt ht
    have gi := congrArg idx hg
    have hi := congrArg idx hh
    simp only [owner, org_idx, gt, ht] at gi hi
    have hl := genome_path_lane hp
    have ge : block 0 (lane g) = 0 := gi
    have he : block 0 (lane h) = 1 := hi
    rw [hl, he] at ge
    contradiction

def observedOwners (N : Nat) (K : Schedule) (g : Nat) : Option Nat :=
  if g/8 ≤ N then some (owner K g) else none

def Family (K : Schedule) : Prop :=
  K = mixing ∨ ∃ S, 2 ≤ S ∧ S%2=0 ∧ K = splitting S

/-- No rule on the common complete copy graph and a bounded owner prefix is correct on this family. -/
theorem no_iap_decoder (N : Nat) : ¬ ∃ D : Graph → (Nat → Option Nat) → Prop,
    ∀ K, Family K → (D Genome (observedOwners N K) ↔ IAP (Edge K) Whole) := by
  rintro ⟨D, hD⟩
  let S := 2*(N+1)
  have he : observedOwners N (splitting S) = observedOwners N mixing := by
    funext g
    by_cases hg : g/8 ≤ N
    · simp only [observedOwners, if_pos hg]
      rw [prefix_owner_agreement S g (by dsimp [S]; omega)]
    · simp [observedOwners, hg]
  have hp := (hD mixing (Or.inl rfl)).mpr mixing_iap
  have hn := hD (splitting S) (Or.inr ⟨S, by dsimp [S]; omega, by dsimp [S]; omega, rfl⟩)
  rw [he] at hn
  exact splitting_not_iap S (by dsimp [S]; omega) (hn.mp hp)

theorem edge_strict {K : Schedule} {u v : Nat} (h : Edge K u v) : u < v := by
  have := h.1
  omega

theorem children_finite (K : Schedule) (u : Nat) : FiniteSupport (Edge K u) := by
  apply (finiteSupport_iff_bounded _).mpr
  refine ⟨4*(u/4+2), ?_⟩
  intro v h
  have := h.1
  omega

theorem natural_biosphere (K : Schedule) : NaturalDateBiosphere (Edge K) :=
  ⟨fun _ _ h => edge_strict h, finite_birthdate_prefix, children_finite K, whole_infinite⟩

theorem founders_exactly_four (K : Schedule) (hK : ∀ t, Allowed (K t) (K (t+1))) (v : Nat) :
    (¬ ∃ u, Edge K u v) ↔ v < 4 := by
  constructor
  · intro hn
    by_cases hv : v < 4
    · exact hv
    · obtain ⟨a, b, _, hp⟩ := two_parents K hK v (by omega)
      exact False.elim (hn ⟨a, (hp a).mpr (Or.inl rfl)⟩)
  · rintro hv ⟨u, h⟩
    have := h.1
    omega

theorem block_sex_same : ∀ l : Fin 8, (block 1 l).val%2 = (block 2 l).val%2 := by decide

/-- Even adding these per-copy organism-sex labels leaves the two histories identical. -/
theorem same_copy_sex (S g : Nat) :
    (idx (owner mixing g)).val%2 = (idx (owner (splitting S) g)).val%2 := by
  simp only [owner, org_idx]
  by_cases hs : g/8 ≤ S
  · simp [splitting, hs]
  · simp only [splitting, if_neg hs]
    by_cases ht : (g/8)%2=0
    · simp [mixing, ht]
    · simp only [mixing, if_neg ht]
      exact block_sex_same (lane g)

/-- The scoped counterexample, agreeing on ownership through any prescribed finite generation. -/
theorem constrained_counterexample (N : Nat) : ∃ S : Nat,
    2 ≤ S ∧ S%2=0 ∧
    (∀ g, g/8 ≤ N → owner (splitting S) g = owner mixing g) ∧
    WeaklyConnected (Edge mixing) Whole ∧ WeaklyConnected (Edge (splitting S)) Whole ∧
    TwoParents (Edge mixing) ∧ TwoParents (Edge (splitting S)) ∧
    TwoChildren (Edge mixing) ∧ TwoChildren (Edge (splitting S)) ∧
    MaximalSpecieslike (Edge mixing) Whole ∧ ¬ Specieslike (Edge (splitting S)) Whole ∧
    Inspecies (Edge mixing) Whole ∧ ¬ Inspecies (Edge (splitting S)) Whole ∧
    IAP (Edge mixing) Whole ∧ ¬ IAP (Edge (splitting S)) Whole := by
  let S := 2*(N+1)
  have hS : S%2=0 := by dsimp [S]; omega
  have hS2 : 2 ≤ S := by dsimp [S]; omega
  refine ⟨S, hS2, hS, ?_, mixing_connected, splitting_connected S hS hS2,
    (pedigrees_two_parents S hS).1, (pedigrees_two_parents S hS).2,
    (pedigrees_two_children S hS).1, (pedigrees_two_children S hS).2,
    mixing_maximal, splitting_not_specieslike S hS, mixing_inspecies,
    splitting_not_inspecies S hS, mixing_iap, splitting_not_iap S hS⟩
  intro g hg
  exact prefix_owner_agreement S g (by dsimp [S]; omega)

end PairingCore
