import WongSimplification
import Mathlib.Data.List.Sort

/-!
# Canonical interval merging for finite genomic edge records

An executable list algorithm merges touching proper half-open intervals.
For ordered, nonoverlapping input it produces the unique strictly separated
list with the same coordinate membership. The GARG adapter later in this file
uses classical finite-set enumeration and activity decisions and is explicitly
noncomputable; the list algorithm itself does not use choice.
-/

namespace WongIntervalCanonicalization
open WongGARG AncestryViews WongIntervalNormalization
universe u v
variable {Coord : Type v} [LinearOrder Coord]

/-- Membership in the union represented by a list of intervals. -/
def Covers (L : List (Interval Coord)) (x : Coord) : Prop :=
  ∃ I ∈ L, I.Contains x

@[simp] theorem covers_nil (x : Coord) : ¬ Covers ([] : List (Interval Coord)) x := by
  simp [Covers]

@[simp] theorem covers_cons (I : Interval Coord) (L : List (Interval Coord)) (x : Coord) :
    Covers (I :: L) x ↔ I.Contains x ∨ Covers L x := by
  simp [Covers, or_and_right, exists_or]

/-- Weak separation permits touching endpoints; strong separation forbids them. -/
def Ordered (L : List (Interval Coord)) : Prop :=
  L.Pairwise (fun I J => I.hi ≤ J.lo)

def Separated (L : List (Interval Coord)) : Prop :=
  L.Pairwise (fun I J => I.hi < J.lo)

/-- Join two exactly touching intervals. Their outer endpoints are reused. -/
def join (I J : Interval Coord) (touch : I.hi = J.lo) : Interval Coord where
  lo := I.lo
  hi := J.hi
  proper := lt_trans I.proper (touch.symm ▸ J.proper)

theorem join_contains (I J : Interval Coord) (h : I.hi = J.lo) (x : Coord) :
    (join I J h).Contains x ↔ I.Contains x ∨ J.Contains x := by
  change (I.lo ≤ x ∧ x < J.hi) ↔
    (I.lo ≤ x ∧ x < I.hi) ∨ (J.lo ≤ x ∧ x < J.hi)
  constructor
  · intro hx
    by_cases hxi : x < I.hi
    · exact Or.inl ⟨hx.1, hxi⟩
    · exact Or.inr ⟨h ▸ le_of_not_gt hxi, hx.2⟩
  · rintro (hx | hx)
    · exact ⟨hx.1, lt_trans hx.2 (h.symm ▸ J.proper)⟩
    · exact ⟨le_trans I.proper.le (h.symm ▸ hx.1), hx.2⟩

/-- Prepend one interval, merging with the head exactly when endpoints touch. -/
def prepend (I : Interval Coord) : List (Interval Coord) → List (Interval Coord)
  | [] => [I]
  | J :: L => if h : I.hi = J.lo then join I J h :: L else I :: J :: L

/-- Explicit right-to-left interval merge; no choice or existence oracle. -/
def mergeAdjacent : List (Interval Coord) → List (Interval Coord)
  | [] => []
  | I :: L => prepend I (mergeAdjacent L)

theorem prepend_covers (I : Interval Coord) (L : List (Interval Coord)) (x : Coord) :
    Covers (prepend I L) x ↔ I.Contains x ∨ Covers L x := by
  cases L with
  | nil => simp [prepend]
  | cons J L =>
    by_cases h : I.hi = J.lo
    · simp [prepend, h, join_contains, or_assoc]
    · simp [prepend, h]

/-- Every merge preserves coordinate semantics, even before an ordering premise. -/
theorem mergeAdjacent_covers (L : List (Interval Coord)) (x : Coord) :
    Covers (mergeAdjacent L) x ↔ Covers L x := by
  induction L with
  | nil => rfl
  | cons I L ih => simpa only [mergeAdjacent, prepend_covers, covers_cons] using or_congr Iff.rfl ih

theorem prepend_lo {I J : Interval Coord} {L : List (Interval Coord)}
    (hJ : J ∈ prepend I L) : J.lo = I.lo ∨ ∃ K ∈ L, J.lo = K.lo := by
  cases L with
  | nil =>
    have e : J = I := by simpa [prepend] using hJ
    subst J
    exact Or.inl rfl
  | cons K L =>
    by_cases h : I.hi = K.lo
    · simp only [prepend, dif_pos h, List.mem_cons] at hJ
      rcases hJ with rfl | hJ
      · exact Or.inl rfl
      · exact Or.inr ⟨J, List.mem_cons_of_mem K hJ, rfl⟩
    · simp only [prepend, dif_neg h] at hJ
      rcases List.mem_cons.mp hJ with rfl | hJ
      · exact Or.inl rfl
      · exact Or.inr ⟨J, hJ, rfl⟩

theorem prepend_hi {I J : Interval Coord} {L : List (Interval Coord)}
    (hJ : J ∈ prepend I L) : J.hi = I.hi ∨ ∃ K ∈ L, J.hi = K.hi := by
  cases L with
  | nil =>
    have e : J = I := by simpa [prepend] using hJ
    subst J
    exact Or.inl rfl
  | cons K L =>
    by_cases h : I.hi = K.lo
    · simp only [prepend, dif_pos h, List.mem_cons] at hJ
      rcases hJ with rfl | hJ
      · exact Or.inr ⟨K, List.mem_cons_self, rfl⟩
      · exact Or.inr ⟨J, List.mem_cons_of_mem K hJ, rfl⟩
    · simp only [prepend, dif_neg h] at hJ
      rcases List.mem_cons.mp hJ with rfl | hJ
      · exact Or.inl rfl
      · exact Or.inr ⟨J, hJ, rfl⟩

/-- A merged lower endpoint is a lower endpoint already supplied in the input. -/
theorem mergeAdjacent_lo (L : List (Interval Coord)) {J : Interval Coord}
    (hJ : J ∈ mergeAdjacent L) : ∃ I ∈ L, J.lo = I.lo := by
  induction L generalizing J with
  | nil => simp [mergeAdjacent] at hJ
  | cons I L ih =>
    rcases prepend_lo hJ with h | ⟨K, hK, h⟩
    · exact ⟨I, List.mem_cons_self, h⟩
    · obtain ⟨T, hT, e⟩ := ih hK
      exact ⟨T, List.mem_cons_of_mem I hT, h.trans e⟩

/-- A merged upper endpoint is an upper endpoint already supplied in the input. -/
theorem mergeAdjacent_hi (L : List (Interval Coord)) {J : Interval Coord}
    (hJ : J ∈ mergeAdjacent L) : ∃ I ∈ L, J.hi = I.hi := by
  induction L generalizing J with
  | nil => simp [mergeAdjacent] at hJ
  | cons I L ih =>
    rcases prepend_hi hJ with h | ⟨K, hK, h⟩
    · exact ⟨I, List.mem_cons_self, h⟩
    · obtain ⟨T, hT, e⟩ := ih hK
      exact ⟨T, List.mem_cons_of_mem I hT, h.trans e⟩

private theorem prepend_separated (I : Interval Coord) (L : List (Interval Coord))
    (hL : Separated L) (hI : ∀ J ∈ L, I.hi ≤ J.lo) : Separated (prepend I L) := by
  cases L with
  | nil => simp [prepend, Separated]
  | cons J L =>
    obtain ⟨hJ, htail⟩ := List.pairwise_cons.mp hL
    by_cases h : I.hi = J.lo
    · simp only [prepend, dif_pos h]
      apply List.pairwise_cons.mpr
      exact ⟨hJ, htail⟩
    · change Separated (if h : I.hi = J.lo then join I J h :: L else I :: J :: L)
      rw [dif_neg h]
      apply List.pairwise_cons.mpr
      refine ⟨?_, hL⟩
      intro K hK
      rcases List.mem_cons.mp hK with hKJ | hK
      · subst K
        exact lt_of_le_of_ne (hI J List.mem_cons_self) h
      · exact lt_trans (lt_of_le_of_lt (hI J List.mem_cons_self) J.proper) (hJ K hK)

/-- Ordered nonoverlapping input becomes sorted with a strict gap between records. -/
theorem mergeAdjacent_separated (L : List (Interval Coord)) (hL : Ordered L) :
    Separated (mergeAdjacent L) := by
  induction L with
  | nil => simp [mergeAdjacent, Separated]
  | cons I L ih =>
    obtain ⟨hI, htail⟩ := List.pairwise_cons.mp hL
    apply prepend_separated I (mergeAdjacent L) (ih htail)
    intro J hJ
    obtain ⟨K, hK, e⟩ := mergeAdjacent_lo L hJ
    rw [e]
    exact hI K hK

/-- Already separated input is an exact fixed point, including storage order. -/
theorem mergeAdjacent_of_separated (L : List (Interval Coord)) (hL : Separated L) :
    mergeAdjacent L = L := by
  induction L with
  | nil => rfl
  | cons I L ih =>
    obtain ⟨hI, htail⟩ := List.pairwise_cons.mp hL
    simp only [mergeAdjacent, ih htail]
    cases L with
    | nil => rfl
    | cons J L => exact dif_neg (ne_of_lt (hI J List.mem_cons_self))

theorem mergeAdjacent_idempotent (L : List (Interval Coord)) (hL : Ordered L) :
    mergeAdjacent (mergeAdjacent L) = mergeAdjacent L :=
  mergeAdjacent_of_separated _ (mergeAdjacent_separated L hL)

private theorem covered_ge_head {I : Interval Coord} {L : List (Interval Coord)}
    (hL : Separated (I :: L)) {x : Coord} (hx : Covers (I :: L) x) : I.lo ≤ x := by
  rcases (covers_cons I L x).mp hx with hx | ⟨J, hJ, hx⟩
  · exact hx.1
  · exact le_trans (lt_trans I.proper ((List.pairwise_cons.mp hL).1 J hJ)).le hx.1

private theorem head_hi_uncovered {I : Interval Coord} {L : List (Interval Coord)}
    (hL : Separated (I :: L)) : ¬ Covers (I :: L) I.hi := by
  rintro ⟨J, hJ, hx⟩
  rcases List.mem_cons.mp hJ with rfl | hJ
  · exact lt_irrefl _ hx.2
  · exact (not_le_of_gt ((List.pairwise_cons.mp hL).1 J hJ)) hx.1

private theorem interval_ext {I J : Interval Coord} (hl : I.lo = J.lo) (hh : I.hi = J.hi) :
    I = J := by
  cases I
  cases J
  cases hl
  cases hh
  rfl

/-- Strictly separated interval lists are uniquely determined by full membership
at every coordinate; density of the coordinate order is not required. -/
theorem separated_semantic_unique (L M : List (Interval Coord))
    (hL : Separated L) (hM : Separated M)
    (heq : ∀ x, Covers L x ↔ Covers M x) : L = M := by
  induction L generalizing M with
  | nil =>
    cases M with
    | nil => rfl
    | cons J M =>
      have h := (heq J.lo).mpr ⟨J, List.mem_cons_self, le_rfl, J.proper⟩
      exact False.elim (covers_nil _ h)
  | cons I L ih =>
    cases M with
    | nil =>
      have h := (heq I.lo).mp ⟨I, List.mem_cons_self, le_rfl, I.proper⟩
      exact False.elim (covers_nil _ h)
    | cons J M =>
      have hlo : I.lo = J.lo := le_antisymm
        (covered_ge_head hL ((heq J.lo).mpr ⟨J, List.mem_cons_self, le_rfl, J.proper⟩))
        (covered_ge_head hM ((heq I.lo).mp ⟨I, List.mem_cons_self, le_rfl, I.proper⟩))
      have hhi : I.hi = J.hi := by
        rcases lt_trichotomy I.hi J.hi with h | h | h
        · exact False.elim (head_hi_uncovered hL ((heq I.hi).mpr
            ⟨J, List.mem_cons_self, hlo ▸ I.proper.le, h⟩))
        · exact h
        · exact False.elim (head_hi_uncovered hM ((heq J.hi).mp
            ⟨I, List.mem_cons_self, hlo.symm ▸ J.proper.le, h⟩))
      have hIJ := interval_ext hlo hhi
      subst J
      congr 1
      apply ih M (List.pairwise_cons.mp hL).2 (List.pairwise_cons.mp hM).2
      intro x
      constructor
      · intro hx
        have hnot : ¬ I.Contains x := by
          obtain ⟨K, hK, hxK⟩ := hx
          intro hxI
          exact (not_lt_of_ge (le_trans ((List.pairwise_cons.mp hL).1 K hK).le hxK.1)) hxI.2
        exact ((covers_cons I M x).mp ((heq x).mp ((covers_cons I L x).mpr (Or.inr hx)))).resolve_left hnot
      · intro hx
        have hnot : ¬ I.Contains x := by
          obtain ⟨K, hK, hxK⟩ := hx
          intro hxI
          exact (not_lt_of_ge (le_trans ((List.pairwise_cons.mp hM).1 K hK).le hxK.1)) hxI.2
        exact ((covers_cons I L x).mp ((heq x).mpr ((covers_cons I M x).mpr (Or.inr hx)))).resolve_left hnot

/-- Different subdivisions of the same coordinate set produce the same output. -/
theorem mergeAdjacent_semantic_unique (L M : List (Interval Coord))
    (hL : Ordered L) (hM : Ordered M) (heq : ∀ x, Covers L x ↔ Covers M x) :
    mergeAdjacent L = mergeAdjacent M := by
  apply separated_semantic_unique _ _ (mergeAdjacent_separated L hL) (mergeAdjacent_separated M hM)
  intro x
  exact (mergeAdjacent_covers L x).trans ((heq x).trans (mergeAdjacent_covers M x).symm)

/-- Any two different output intervals have an actual strict endpoint gap. -/
theorem separated_gap {L : List (Interval Coord)} (hL : Separated L)
    {I J : Interval Coord} (hI : I ∈ L) (hJ : J ∈ L) (hne : I ≠ J) :
    I.hi < J.lo ∨ J.hi < I.lo := by
  induction L with
  | nil => simp at hI
  | cons K L ih =>
    obtain ⟨hK, htail⟩ := List.pairwise_cons.mp hL
    rcases List.mem_cons.mp hI with hIK | hIt
    · subst I
      rcases List.mem_cons.mp hJ with hJK | hJt
      · exact False.elim (hne hJK.symm)
      · exact Or.inl (hK J hJt)
    · rcases List.mem_cons.mp hJ with hJK | hJt
      · subst J
        exact Or.inr (hK I hIt)
      · exact ih htail hIt hJt

theorem separated_disjoint {L : List (Interval Coord)} (hL : Separated L)
    {I J : Interval Coord} (hI : I ∈ L) (hJ : J ∈ L) (hne : I ≠ J) : I.Disjoint J := by
  intro x hx
  rcases separated_gap hL hI hJ hne with h | h
  · exact (not_lt_of_ge (le_trans h.le hx.2.1)) hx.1.2
  · exact (not_lt_of_ge (le_trans h.le hx.1.1)) hx.2.2

/-! The finite-set/GARG envelope below is noncomputable. Input records use
abstract Finsets and arbitrary propositions for coordinate activity. It invokes
the executable merge above after selecting and sorting a finite enumeration. -/
noncomputable section
local instance (α : Type*) : DecidableEq α := Classical.decEq α
local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Sort a finite family by its lower endpoint. -/
def sortedRegions (F : Finset (Interval Coord)) : List (Interval Coord) :=
  F.toList.mergeSort (fun I J => decide (I.lo ≤ J.lo))

@[simp] theorem mem_sortedRegions (F : Finset (Interval Coord)) (I : Interval Coord) :
    I ∈ sortedRegions F ↔ I ∈ F := by
  simp [sortedRegions]

theorem sortedRegions_ordered (F : Finset (Interval Coord))
    (hF : ∀ I ∈ F, ∀ J ∈ F, I ≠ J → I.Disjoint J) : Ordered (sortedRegions F) := by
  have hs : (sortedRegions F).Pairwise (fun I J => I.lo ≤ J.lo) := by
    have hh := List.pairwise_mergeSort
      (le := fun I J : Interval Coord => decide (I.lo ≤ J.lo))
      (by intro a b c hab hbc; simpa using le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))
      (by intro a b; simpa using le_total a.lo b.lo) F.toList
    simpa only [sortedRegions, decide_eq_true_eq] using hh
  have hn : (sortedRegions F).Nodup :=
    (List.mergeSort_perm F.toList _).nodup_iff.mpr F.nodup_toList
  apply (hs.and hn).imp_of_mem
  intro I J hI hJ h
  by_contra hnot
  have hlt : J.lo < I.hi := lt_of_not_ge hnot
  exact hF I ((mem_sortedRegions F I).mp hI) J ((mem_sortedRegions F J).mp hJ) h.2
    J.lo ⟨⟨h.1, hlt⟩, ⟨le_rfl, J.proper⟩⟩

/-- The canonical maximal-interval list for a disjoint finite interval family. -/
def canonicalRegions (F : Finset (Interval Coord)) : List (Interval Coord) :=
  mergeAdjacent (sortedRegions F)

theorem canonicalRegions_covers (F : Finset (Interval Coord)) (x : Coord) :
    Covers (canonicalRegions F) x ↔ ∃ I ∈ F, I.Contains x := by
  rw [canonicalRegions, mergeAdjacent_covers]
  simp [Covers]

theorem canonicalRegions_separated (F : Finset (Interval Coord))
    (hF : ∀ I ∈ F, ∀ J ∈ F, I ≠ J → I.Disjoint J) : Separated (canonicalRegions F) :=
  mergeAdjacent_separated _ (sortedRegions_ordered F hF)

theorem canonicalRegions_endpoints (F : Finset (Interval Coord)) {J : Interval Coord}
    (hJ : J ∈ canonicalRegions F) :
    (∃ I ∈ F, J.lo = I.lo) ∧ (∃ I ∈ F, J.hi = I.hi) := by
  obtain ⟨I, hI, hlo⟩ := mergeAdjacent_lo (sortedRegions F) hJ
  obtain ⟨K, hK, hhi⟩ := mergeAdjacent_hi (sortedRegions F) hJ
  exact ⟨⟨I, (mem_sortedRegions F I).mp hI, hlo⟩,
    ⟨K, (mem_sortedRegions F K).mp hK, hhi⟩⟩

theorem canonicalRegions_unique (F H : Finset (Interval Coord))
    (hF : ∀ I ∈ F, ∀ J ∈ F, I ≠ J → I.Disjoint J)
    (hH : ∀ I ∈ H, ∀ J ∈ H, I ≠ J → I.Disjoint J)
    (heq : ∀ x, (∃ I ∈ F, I.Contains x) ↔ ∃ I ∈ H, I.Contains x) :
    canonicalRegions F = canonicalRegions H := by
  apply separated_semantic_unique _ _ (canonicalRegions_separated F hF) (canonicalRegions_separated H hH)
  intro x
  exact (canonicalRegions_covers F x).trans ((heq x).trans (canonicalRegions_covers H x).symm)

variable {Node : Type u} [Fintype Node]
namespace CellPresentation
variable {R : Coord → Node → Node → Prop} (C : WongIntervalNormalization.CellPresentation R)

/-- A deterministic parent-child list of maximal annotated coordinate intervals,
with classical preparation of its finite source cell family. -/
def serializedRegions (a b : Node) : List (Interval Coord) :=
  canonicalRegions (C.record a b).regions

theorem serializedRegions_separated (a b : Node) : Separated (serializedRegions C a b) :=
  canonicalRegions_separated _ (C.record a b).disjoint

theorem serializedRegions_covers (x : Coord) (a b : Node) :
    Covers (serializedRegions C a b) x ↔ R x a b := by
  rw [serializedRegions, canonicalRegions_covers]
  constructor
  · rintro ⟨I, hI, hx⟩
    obtain ⟨hcell, hR⟩ := (C.mem_record_regions a b I).mp hI
    exact (C.constant I hcell x hx a b).mpr hR
  · intro hR
    obtain ⟨I, hI, hx⟩ := C.covered x a b hR
    exact ⟨I, (C.mem_record_regions a b I).mpr
      ⟨hI, (C.constant I hI x hx a b).mp hR⟩, hx⟩

/-- Actual record with touching pieces merged, rather than only grouped cells. -/
def canonicalRecord (a b : Node) : EdgeRecord Node Coord where
  parent := a
  child := b
  regions := (serializedRegions C a b).toFinset
  disjoint := by
    intro I hI J hJ hne
    exact separated_disjoint (serializedRegions_separated C a b)
      (List.mem_toFinset.mp hI) (List.mem_toFinset.mp hJ) hne

@[simp] theorem canonicalRecord_covers (x : Coord) (a b : Node) :
    (canonicalRecord C a b).Covers x ↔ R x a b := by
  simpa only [EdgeRecord.Covers, canonicalRecord, List.mem_toFinset, Covers]
    using serializedRegions_covers C x a b

def canonicalRecords : Finset (EdgeRecord Node Coord) :=
  C.activePairs.image (fun pair => canonicalRecord C pair.1 pair.2)

theorem canonicalRecords_nonempty {e : EdgeRecord Node Coord}
    (he : e ∈ canonicalRecords C) : e.regions.Nonempty := by
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨I, hI⟩ := (Finset.mem_filter.mp hab).2
  have hIR := ((C.mem_record_regions a b I).mp hI).2
  obtain ⟨J, hJ, _⟩ := (canonicalRecord_covers C I.lo a b).mpr hIR
  exact ⟨J, hJ⟩

theorem canonicalRecords_at (x : Coord) (a b : Node) :
    (∃ e ∈ canonicalRecords C, e.parent = a ∧ e.child = b ∧ e.Covers x) ↔ R x a b := by
  constructor
  · rintro ⟨e, he, ha, hb, hx⟩
    obtain ⟨⟨p, c⟩, _, rfl⟩ := Finset.mem_image.mp he
    change p = a at ha
    change c = b at hb
    subst p
    subst c
    exact (canonicalRecord_covers C x a b).mp hx
  · intro hx
    obtain ⟨I, hI, hIx⟩ := C.covered x a b hx
    have hmem : I ∈ (C.record a b).regions :=
      (C.mem_record_regions a b I).mpr ⟨hI, (C.constant I hI x hIx a b).mp hx⟩
    refine ⟨canonicalRecord C a b, ?_, rfl, rfl, (canonicalRecord_covers C x a b).mpr hx⟩
    exact Finset.mem_image.mpr ⟨(a,b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, I, hmem⟩, rfl⟩

theorem canonicalRecords_topology (a b : Node) :
    RecordTopology (canonicalRecords C) a b ↔ EraseIndex R a b := by
  constructor
  · rintro ⟨e, he, ha, hb⟩
    obtain ⟨I, hI⟩ := canonicalRecords_nonempty C he
    exact ⟨I.lo, (canonicalRecords_at C I.lo a b).mp
      ⟨e, he, ha, hb, I, hI, le_rfl, I.proper⟩⟩
  · rintro ⟨x, hx⟩
    obtain ⟨e, he, ha, hb, _⟩ := (canonicalRecords_at C x a b).mpr hx
    exact ⟨e, he, ha, hb⟩

/-- The completed finite record representation, with maximal intervals per pair. -/
def canonicalGARG (samples : Finset Node) (acyclic : UnionAcyclic R) : GARG Node Coord where
  samples := samples
  records := canonicalRecords C
  acyclic := by
    intro a h
    exact acyclic a (reach_mono (fun p c he => (canonicalRecords_topology C p c).mp he) h)

theorem canonicalGARG_at (samples : Finset Node) (acyclic : UnionAcyclic R)
    (x : Coord) (a b : Node) : (canonicalGARG C samples acyclic).AtLocus x a b ↔ R x a b :=
  canonicalRecords_at C x a b

theorem canonicalGARG_canonical (samples : Finset Node) (acyclic : UnionAcyclic R) :
    (canonicalGARG C samples acyclic).CanonicalRecords := by
  intro e he f hf hp hc
  obtain ⟨⟨a,b⟩, _, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨⟨c,d⟩, _, rfl⟩ := Finset.mem_image.mp hf
  change a = c at hp
  change b = d at hc
  subst c
  subst d
  rfl

theorem canonicalGARG_maximal (samples : Finset Node) (acyclic : UnionAcyclic R) :
    ∀ e ∈ (canonicalGARG C samples acyclic).records,
      ∀ I ∈ e.regions, ∀ J ∈ e.regions, I ≠ J → I.hi < J.lo ∨ J.hi < I.lo := by
  intro e he I hI J hJ hne
  obtain ⟨⟨a,b⟩, _, rfl⟩ := Finset.mem_image.mp he
  exact separated_gap (serializedRegions_separated C a b)
    (List.mem_toFinset.mp hI) (List.mem_toFinset.mp hJ) hne

theorem canonicalGARG_endpoints (samples : Finset Node) (acyclic : UnionAcyclic R)
    (B : Finset Coord) (endpoints : ∀ I ∈ C.cells, I.lo ∈ B ∧ I.hi ∈ B) :
    (canonicalGARG C samples acyclic).breakpoints ⊆ B := by
  intro z hz
  obtain ⟨e, he, hreg⟩ := Finset.mem_biUnion.mp hz
  obtain ⟨⟨a,b⟩, _, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨J, hJ, hzJ⟩ := Finset.mem_biUnion.mp hreg
  have hm : J ∈ canonicalRegions (C.record a b).regions := List.mem_toFinset.mp hJ
  obtain ⟨⟨I, hI, hlo⟩, ⟨K, hK, hhi⟩⟩ := canonicalRegions_endpoints _ hm
  have hIc := ((C.mem_record_regions a b I).mp hI).1
  have hKc := ((C.mem_record_regions a b K).mp hK).1
  have heq : z = J.lo ∨ z = J.hi := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hzJ
  rcases heq with rfl | rfl
  · rw [hlo]
    exact (endpoints I hIc).1
  · rw [hhi]
    exact (endpoints K hKc).2

end CellPresentation

/-- Canonical record reconstruction of an arbitrary finite interval GARG. Empty
annotations are omitted; node IDs and samples are retained. -/
def canonicalize (G : GARG Node Coord) : GARG Node Coord :=
  CellPresentation.canonicalGARG (WongSimplification.automaticPresentation G)
    G.samples (garg_union_acyclic G)

theorem canonicalize_at (G : GARG Node Coord) (x : Coord) (a b : Node) :
    (canonicalize G).AtLocus x a b ↔ G.AtLocus x a b :=
  CellPresentation.canonicalGARG_at _ _ _ x a b

theorem canonicalize_breakpoints (G : GARG Node Coord) :
    (canonicalize G).breakpoints ⊆ G.breakpoints := by
  apply CellPresentation.canonicalGARG_endpoints
  intro I hI
  exact ⟨((WongBreakpointCells.mem_cells_iff G.breakpoints I).mp hI).1,
    ((WongBreakpointCells.mem_cells_iff G.breakpoints I).mp hI).2.1⟩

theorem canonicalize_nonempty (G : GARG Node Coord) : (canonicalize G).NonemptyAnnotations := by
  intro e he
  exact CellPresentation.canonicalRecords_nonempty _ he

theorem canonicalize_canonical (G : GARG Node Coord) : (canonicalize G).CanonicalRecords :=
  CellPresentation.canonicalGARG_canonical _ _ _

theorem canonicalize_maximal (G : GARG Node Coord) :
    ∀ e ∈ (canonicalize G).records, ∀ I ∈ e.regions, ∀ J ∈ e.regions,
      I ≠ J → I.hi < J.lo ∨ J.hi < I.lo :=
  CellPresentation.canonicalGARG_maximal _ _ _

/-- Reconstruction is independent of irrelevant subdivision endpoints. -/
theorem serialized_semantic_unique {R Q : Coord → Node → Node → Prop}
    (C : WongIntervalNormalization.CellPresentation R)
    (D : WongIntervalNormalization.CellPresentation Q)
    (heq : ∀ x a b, R x a b ↔ Q x a b) (a b : Node) :
    CellPresentation.serializedRegions C a b = CellPresentation.serializedRegions D a b := by
  apply separated_semantic_unique _ _
    (CellPresentation.serializedRegions_separated C a b)
    (CellPresentation.serializedRegions_separated D a b)
  intro x
  exact (CellPresentation.serializedRegions_covers C x a b).trans
    ((heq x a b).trans (CellPresentation.serializedRegions_covers D x a b).symm)

/-- Empty coordinate activity has the empty canonical list. -/
theorem serialized_empty {R : Coord → Node → Node → Prop}
    (C : WongIntervalNormalization.CellPresentation R) (a b : Node)
    (hempty : ∀ x, ¬ R x a b) : CellPresentation.serializedRegions C a b = [] := by
  apply separated_semantic_unique _ _ (CellPresentation.serializedRegions_separated C a b)
    (by simp [Separated])
  intro x
  simp only [CellPresentation.serializedRegions_covers]
  exact iff_of_false (hempty x) (covers_nil x)

private theorem canonicalRecord_eq {R Q : Coord → Node → Node → Prop}
    (C : WongIntervalNormalization.CellPresentation R)
    (D : WongIntervalNormalization.CellPresentation Q)
    (heq : ∀ x a b, R x a b ↔ Q x a b) (a b : Node) :
    CellPresentation.canonicalRecord C a b = CellPresentation.canonicalRecord D a b := by
  have h := serialized_semantic_unique C D heq a b
  unfold CellPresentation.canonicalRecord
  congr 1
  exact congrArg List.toFinset h

private theorem canonicalRecords_mem_iff {R : Coord → Node → Node → Prop}
    (C : WongIntervalNormalization.CellPresentation R) (e : EdgeRecord Node Coord) :
    e ∈ CellPresentation.canonicalRecords C ↔
      ∃ a b, (∃ x, R x a b) ∧ e = CellPresentation.canonicalRecord C a b := by
  constructor
  · intro he
    obtain ⟨⟨a,b⟩, hab, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨I, hI⟩ := (Finset.mem_filter.mp hab).2
    exact ⟨a, b, ⟨I.lo, ((C.mem_record_regions a b I).mp hI).2⟩, rfl⟩
  · rintro ⟨a,b, ⟨x,hx⟩, rfl⟩
    obtain ⟨I, hI, hIx⟩ := C.covered x a b hx
    have hm := (C.mem_record_regions a b I).mpr ⟨hI, (C.constant I hI x hIx a b).mp hx⟩
    exact Finset.mem_image.mpr ⟨(a,b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, I, hm⟩, rfl⟩

private theorem canonicalRecords_eq {R Q : Coord → Node → Node → Prop}
    (C : WongIntervalNormalization.CellPresentation R)
    (D : WongIntervalNormalization.CellPresentation Q)
    (heq : ∀ x a b, R x a b ↔ Q x a b) :
    CellPresentation.canonicalRecords C = CellPresentation.canonicalRecords D := by
  ext e
  rw [canonicalRecords_mem_iff, canonicalRecords_mem_iff]
  constructor
  · rintro ⟨a,b,⟨x,hx⟩,he⟩
    exact ⟨a,b,⟨x,(heq x a b).mp hx⟩,he.trans (canonicalRecord_eq C D heq a b)⟩
  · rintro ⟨a,b,⟨x,hx⟩,he⟩
    exact ⟨a,b,⟨x,(heq x a b).mpr hx⟩,he.trans (canonicalRecord_eq C D heq a b).symm⟩

private theorem garg_ext {G H : GARG Node Coord} (hs : G.samples = H.samples)
    (hr : G.records = H.records) : G = H := by
  cases G
  cases H
  cases hs
  cases hr
  rfl

/-- Full canonical graph output is uniquely determined by samples and indexed
edge semantics, even when inputs differ in subdivision or empty records. -/
theorem canonicalize_semantic_unique (G H : GARG Node Coord)
    (hs : G.samples = H.samples)
    (heq : ∀ x a b, G.AtLocus x a b ↔ H.AtLocus x a b) :
    canonicalize G = canonicalize H := by
  apply garg_ext (G := canonicalize G) (H := canonicalize H) hs
  exact canonicalRecords_eq (WongSimplification.automaticPresentation G)
    (WongSimplification.automaticPresentation H) heq

/-- Canonical graph reconstruction is an exact fixed point after one pass. -/
theorem canonicalize_idempotent (G : GARG Node Coord) :
    canonicalize (canonicalize G) = canonicalize G :=
  canonicalize_semantic_unique _ _ rfl (canonicalize_at G)

/-- Topology of the output consists precisely of pairs active somewhere.
Topology-only records with no genomic interval are intentionally omitted. -/
theorem canonicalize_topology (G : GARG Node Coord) (a b : Node) :
    (canonicalize G).Topology a b ↔ ∃ x, G.AtLocus x a b :=
  CellPresentation.canonicalRecords_topology _ a b

end
end WongIntervalCanonicalization

/-- A kernel-evaluated example simultaneously checks a chain of touching pieces
and preservation of a genuine gap. -/
theorem WongIntervalCanonicalization.executable_touching_gap_example :
    (WongIntervalCanonicalization.mergeAdjacent
      ([⟨0, 1, by decide⟩, ⟨1, 2, by decide⟩, ⟨2, 3, by decide⟩,
        ⟨5, 6, by decide⟩] : List (WongGARG.Interval Nat))).map
      (fun I => (I.lo, I.hi)) = [(0, 3), (5, 6)] := by decide

#eval (WongIntervalCanonicalization.mergeAdjacent
  ([⟨0, 1, by decide⟩, ⟨1, 2, by decide⟩, ⟨2, 3, by decide⟩,
    ⟨5, 6, by decide⟩] : List (WongGARG.Interval Nat))).map (fun I => (I.lo, I.hi))

#print axioms WongIntervalCanonicalization.join_contains
#print axioms WongIntervalCanonicalization.mergeAdjacent_covers
#print axioms WongIntervalCanonicalization.mergeAdjacent_lo
#print axioms WongIntervalCanonicalization.mergeAdjacent_hi
#print axioms WongIntervalCanonicalization.mergeAdjacent_separated
#print axioms WongIntervalCanonicalization.mergeAdjacent_of_separated
#print axioms WongIntervalCanonicalization.mergeAdjacent_idempotent
#print axioms WongIntervalCanonicalization.separated_semantic_unique
#print axioms WongIntervalCanonicalization.mergeAdjacent_semantic_unique
#print axioms WongIntervalCanonicalization.separated_gap
#print axioms WongIntervalCanonicalization.canonicalRegions_covers
#print axioms WongIntervalCanonicalization.canonicalRegions_separated
#print axioms WongIntervalCanonicalization.canonicalRegions_endpoints
#print axioms WongIntervalCanonicalization.canonicalRegions_unique
#print axioms WongIntervalCanonicalization.CellPresentation.serializedRegions_separated
#print axioms WongIntervalCanonicalization.CellPresentation.serializedRegions_covers
#print axioms WongIntervalCanonicalization.CellPresentation.canonicalGARG_at
#print axioms WongIntervalCanonicalization.CellPresentation.canonicalGARG_canonical
#print axioms WongIntervalCanonicalization.CellPresentation.canonicalGARG_maximal
#print axioms WongIntervalCanonicalization.CellPresentation.canonicalGARG_endpoints
#print axioms WongIntervalCanonicalization.canonicalize_at
#print axioms WongIntervalCanonicalization.canonicalize_breakpoints
#print axioms WongIntervalCanonicalization.canonicalize_nonempty
#print axioms WongIntervalCanonicalization.canonicalize_canonical
#print axioms WongIntervalCanonicalization.canonicalize_maximal
#print axioms WongIntervalCanonicalization.serialized_semantic_unique
#print axioms WongIntervalCanonicalization.serialized_empty
#print axioms WongIntervalCanonicalization.canonicalize_semantic_unique
#print axioms WongIntervalCanonicalization.canonicalize_idempotent
#print axioms WongIntervalCanonicalization.canonicalize_topology
#print axioms WongIntervalCanonicalization.executable_touching_gap_example
