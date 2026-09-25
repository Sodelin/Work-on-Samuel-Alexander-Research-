import WongEventEncoding

/-!
# First-step event conversion: normalized decoding and exact boundaries

Wong et al. (2024), Event ARGs, printed pp. 2-4, especially p. 4's
one-to-one claim BEFORE sample resolution. This module treats the event
parent specification only. The inverse is classical, not an executable parser.
-/
namespace WongEventDecoding
open WongEventEncoding WongGARG
universe u v
noncomputable section
local instance (α : Type*) : DecidableEq α := Classical.decEq α
local instance (P : Prop) : Decidable P := Classical.propDecidable P

variable {Node : Type u} {Coord : Type v} [LinearOrder Coord] {lo hi : Coord}

/-- Distinct crossover parents rule out a semantically invisible split. -/
def Normalized (s : ParentSpec Node Coord lo hi) : Prop :=
  match s with
  | .root => True
  | .singleParent _ => True
  | .crossover a b _ _ _ => a ≠ b

/-- Complete local inheritance semantics, including parent identity. -/
def SameLocal (s t : ParentSpec Node Coord lo hi) : Prop :=
  ∀ x p, s.At x p ↔ t.At x p

/-- A crossover between two identical node identities has exactly the local
inheritance of a single parent. Interval record boundaries can still differ. -/
theorem equal_parent_crossover_same_local (a : Node) (cut : Coord)
    (hl : lo < cut) (hr : cut < hi) :
    SameLocal (.crossover a a cut hl hr) (.singleParent a) := by
  intro x p
  constructor
  · intro h
    exact ⟨(ParentSpec.at_parent _ h).elim id id, ParentSpec.at_in_span _ h⟩
  · rintro ⟨hp, hxlo, hxhi⟩
    by_cases hx : x < cut
    · exact Or.inl ⟨hp, hxlo, hx⟩
    · exact Or.inr ⟨hp, le_of_not_gt hx, hxhi⟩

/-- Parent identity at the beginning of the genome distinguishes the left parent. -/
theorem crossover_left_identified (a b c d : Node) (q r : Coord)
    (lq : lo < q) (hq : q < hi) (lr : lo < r) (hr : r < hi)
    (same : SameLocal (.crossover a b q lq hq) (.crossover c d r lr hr)) : a = c := by
  have h := (same lo a).mp (Or.inl ⟨rfl, le_rfl, lq⟩)
  rcases h with h | h
  · exact h.1
  · exact False.elim ((not_le_of_gt lr) h.2.1)

/-- A position at or beyond both interior cuts identifies the right parent. -/
theorem crossover_right_identified (a b c d : Node) (q r : Coord)
    (lq : lo < q) (hq : q < hi) (lr : lo < r) (hr : r < hi)
    (same : SameLocal (.crossover a b q lq hq) (.crossover c d r lr hr)) : b = d := by
  have hmax : max q r < hi := max_lt hq hr
  have h := (same (max q r) b).mp (Or.inr ⟨rfl, le_max_left _ _, hmax⟩)
  rcases h with h | h
  · exact False.elim ((not_lt_of_ge (le_max_right q r)) h.2.2)
  · exact h.1

/-- Full event-parent specification recovery. Unlike cutoff-only recovery,
both ordered parent identities and the constructor are recovered here. -/
theorem normalized_same_local_iff (hspan : lo < hi)
    (s t : ParentSpec Node Coord lo hi) (hs : Normalized s) (ht : Normalized t) :
    SameLocal s t ↔ s = t := by
  constructor
  · intro same
    cases s with
    | root =>
      cases t with
      | root => rfl
      | singleParent a =>
        exact False.elim ((same lo a).mpr ⟨rfl, le_rfl, hspan⟩)
      | crossover a b cut hl hr =>
        exact False.elim ((same lo a).mpr (Or.inl ⟨rfl, le_rfl, hl⟩))
    | singleParent a =>
      cases t with
      | root => exact False.elim ((same lo a).mp ⟨rfl, le_rfl, hspan⟩)
      | singleParent b =>
        have hab := ((same lo a).mp ⟨rfl, le_rfl, hspan⟩).1
        exact congrArg ParentSpec.singleParent hab
      | crossover b c cut hl hr =>
        have hba := ((same lo b).mpr (Or.inl ⟨rfl, le_rfl, hl⟩)).1
        have hca := ((same cut c).mpr (Or.inr ⟨rfl, le_rfl, hr⟩)).1
        exact False.elim (ht (hba.trans hca.symm))
    | crossover a b cut hl hr =>
      cases t with
      | root => exact False.elim ((same lo a).mp (Or.inl ⟨rfl, le_rfl, hl⟩))
      | singleParent c =>
        have hac := ((same lo a).mp (Or.inl ⟨rfl, le_rfl, hl⟩)).1
        have hbc := ((same cut b).mp (Or.inr ⟨rfl, le_rfl, hr⟩)).1
        exact False.elim (hs (hac.trans hbc.symm))
      | crossover c d cut' hl' hr' =>
        have hac := crossover_left_identified a b c d cut cut' hl hr hl' hr' same
        have hbd := crossover_right_identified a b c d cut cut' hl hr hl' hr' same
        subst c
        subst d
        have hcut := ParentSpec.crossover_cut_identified a b hs cut cut' hl hr hl' hr'
          (fun x _ p => same x p)
        subst cut'
        rfl
  · rintro rfl
    exact fun _ _ => Iff.rfl

abbrev NormalizedSpec (Node : Type u) (Coord : Type v) [LinearOrder Coord]
    (lo hi : Coord) := {s : ParentSpec Node Coord lo hi // Normalized s}

/-- Exact interval-record equality implies equal local inheritance. -/
theorem same_local_of_records_eq (hspan : lo < hi) (child : Node)
    (s t : ParentSpec Node Coord lo hi)
    (h : specRecords hspan child s = specRecords hspan child t) : SameLocal s t := by
  intro x p
  have hs := specRecords_at hspan child s x p child
  have ht := specRecords_at hspan child t x p child
  rw [h] at hs
  simpa only [true_and] using hs.symm.trans ht

/-- Injectivity of the first-step encoding on normalized parent specifications. -/
theorem normalized_records_injective (hspan : lo < hi) (child : Node) :
    Function.Injective (fun s : NormalizedSpec Node Coord lo hi =>
      specRecords hspan child s.val) := by
  intro s t h
  apply Subtype.ext
  exact (normalized_same_local_iff hspan s.val t.val s.property t.property).mp
    (same_local_of_records_eq hspan child s.val t.val h)

/-- Only records already proved to lie in the normalized encoder's range.
This is a semantic range witness, not an implementable input-validation algorithm. -/
abbrev EncodedRecords (hspan : lo < hi) (child : Node) :=
  {r : Finset (EdgeRecord Node Coord) //
    ∃ s : NormalizedSpec Node Coord lo hi, specRecords hspan child s.val = r}

def encode (hspan : lo < hi) (child : Node) (s : NormalizedSpec Node Coord lo hi) :
    EncodedRecords hspan child := ⟨specRecords hspan child s.val, s, rfl⟩

/-- Classical inverse on the explicit range. No event times or external metadata. -/
def decode (hspan : lo < hi) (child : Node) (r : EncodedRecords hspan child) :
    NormalizedSpec Node Coord lo hi := Classical.choose r.property

theorem encode_decode (hspan : lo < hi) (child : Node) (r : EncodedRecords hspan child) :
    encode hspan child (decode hspan child r) = r := by
  apply Subtype.ext
  exact Classical.choose_spec r.property

theorem decode_encode (hspan : lo < hi) (child : Node)
    (s : NormalizedSpec Node Coord lo hi) : decode hspan child (encode hspan child s) = s := by
  apply normalized_records_injective hspan child
  exact Classical.choose_spec (encode hspan child s).property

/-- Bijection with the *range*, not with arbitrary gARG records. -/
def normalizedEncodingEquiv (hspan : lo < hi) (child : Node) :
    NormalizedSpec Node Coord lo hi ≃ EncodedRecords hspan child where
  toFun := encode hspan child
  invFun := decode hspan child
  left_inv := decode_encode hspan child
  right_inv := encode_decode hspan child


namespace Graph
variable [Fintype Node]

/-- Every crossover in the finite event graph has distinct parent identities. -/
def Normalized (G : EventGraph Node Coord lo hi) : Prop :=
  ∀ c, WongEventDecoding.Normalized (G.parents c)

/-- The entire parent-specification map is recovered from raw encoded records. -/
theorem parents_identified (G H : EventGraph Node Coord lo hi)
    (hG : Normalized G) (hH : Normalized H) (same : G.records = H.records) :
    G.parents = H.parents := by
  funext c
  apply (normalized_same_local_iff G.span (G.parents c) (H.parents c) (hG c) (hH c)).mp
  intro x p
  have hencG := G.encoded_atLocus ∅ x p c
  have hencH := H.encoded_atLocus ∅ x p c
  have heq : (G.toGARG ∅).AtLocus x p c ↔ (H.toGARG ∅).AtLocus x p c := by
    change (∃ e ∈ G.records, e.parent = p ∧ e.child = c ∧ e.Covers x) ↔
      (∃ e ∈ H.records, e.parent = p ∧ e.child = c ∧ e.Covers x)
    rw [same]
  exact hencG.symm.trans (heq.trans hencH)

/-- With fixed node IDs and span, raw encoding is injective on normalized graphs.
This includes topology and breakpoints; the input structure has no event times. -/
theorem graph_identified (G H : EventGraph Node Coord lo hi)
    (hG : Normalized G) (hH : Normalized H) (same : G.records = H.records) : G = H := by
  have hp := parents_identified G H hG hH same
  cases G
  cases H
  cases hp
  rfl

omit [Fintype Node] in
/-- A normalized single node emits at most one record per parent-child pair. -/
theorem spec_records_canonical (hspan : lo < hi) (child : Node)
    (s : ParentSpec Node Coord lo hi) (hn : WongEventDecoding.Normalized s)
    (e f : EdgeRecord Node Coord) (he : e ∈ specRecords hspan child s)
    (hf : f ∈ specRecords hspan child s) (hp : e.parent = f.parent) : e = f := by
  cases s with
  | root => simp [specRecords] at he
  | singleParent a =>
    simp only [specRecords, Finset.mem_singleton] at he hf
    exact he.trans hf.symm
  | crossover a b cut hl hr =>
    simp only [specRecords, Finset.mem_insert, Finset.mem_singleton] at he hf
    rcases he with rfl | rfl <;> rcases hf with rfl | rfl
    · rfl
    · exact False.elim (hn hp)
    · exact False.elim (hn hp.symm)
    · rfl

/-- Distinct parents yield the gARG's one-record-per-topological-edge condition. -/
theorem encoded_canonical (G : EventGraph Node Coord lo hi) (hG : Normalized G)
    (samples : Finset Node) : (G.toGARG samples).CanonicalRecords := by
  intro e he f hf hp hc
  obtain ⟨c, _, hec⟩ := Finset.mem_biUnion.mp he
  obtain ⟨d, _, hfd⟩ := Finset.mem_biUnion.mp hf
  have hechild : e.child = c :=
    ((specRecords_topology G.span c (G.parents c) e.parent e.child).mp
      ⟨e, hec, rfl, rfl⟩).1
  have hfchild : f.child = d :=
    ((specRecords_topology G.span d (G.parents d) f.parent f.child).mp
      ⟨f, hfd, rfl, rfl⟩).1
  have hcd : c = d := hechild.symm.trans (hc.trans hfchild)
  rw [← hcd] at hfd
  exact spec_records_canonical G.span c (G.parents c) (hG c) e f hec hfd hp

end Graph

/-- Explicit classical binary event conventions. The root is a terminating
common-ancestor node, distinct from an internal common-ancestor node. -/
inductive EventKind where
  | sample
  | commonAncestor
  | recombination
  | root
  deriving DecidableEq

def EventKind.signature : EventKind → Nat × Nat
  | .sample => (1, 0)
  | .commonAncestor => (1, 2)
  | .recombination => (2, 1)
  | .root => (0, 2)

/-- Degree order is (number of parents, number of children). -/
def decodeKind : Nat → Nat → Option EventKind
  | 1, 0 => some .sample
  | 1, 2 => some .commonAncestor
  | 2, 1 => some .recombination
  | 0, 2 => some .root
  | _, _ => none

theorem kind_signature_injective : Function.Injective EventKind.signature := by
  intro a b h
  cases a <;> cases b <;> simp_all [EventKind.signature]

theorem decode_kind_signature (k : EventKind) :
    decodeKind k.signature.1 k.signature.2 = some k := by
  cases k <;> rfl

variable [Fintype Node]

def degrees (R : Node → Node → Prop) (c : Node) : Nat × Nat :=
  ((Finset.univ.filter (fun p => R p c)).card,
   (Finset.univ.filter (fun d => R c d)).card)

/-- A strict binary event adapter, intentionally excluding isolated samples,
pass-through nodes, multiple crossovers and multifurcations. Root degree is (0,2).
It is an extra interface; it is not imposed on every gARG in Wong's general model. -/
structure ClassicalShape (G : EventGraph Node Coord lo hi) where
  normalized : Graph.Normalized G
  kind : Node → EventKind
  arities : ∀ c, degrees G.Topology c = (kind c).signature


/-- Sample designation for the strict classical adapter agrees with leaf kinds. -/
def ClassicalShape.samples {G : EventGraph Node Coord lo hi} (shape : ClassicalShape G) :
    Finset Node := Finset.univ.filter (fun c => shape.kind c = .sample)

def ClassicalShape.toGARG {G : EventGraph Node Coord lo hi} (shape : ClassicalShape G) :
    WongGARG.GARG Node Coord := G.toGARG shape.samples

theorem classical_encoded_sample_iff (G : EventGraph Node Coord lo hi)
    (shape : ClassicalShape G) (c : Node) :
    c ∈ shape.toGARG.samples ↔ shape.kind c = .sample := by
  simp [ClassicalShape.toGARG, EventGraph.toGARG, ClassicalShape.samples]

/-- The source's first conversion preserves all parent and child degrees. -/
theorem encoded_degrees (G : EventGraph Node Coord lo hi) (samples : Finset Node)
    (c : Node) : degrees (G.toGARG samples).Topology c = degrees G.Topology c := by
  unfold degrees
  have heq : (G.toGARG samples).Topology = G.Topology := by
    funext p d
    exact propext (G.encoded_topology samples p d)
  rw [heq]

/-- Under the explicit classical shape, node kinds can be decoded from the
unchanged graph. No labels for events with other arities are invented. -/
theorem encoded_kind_recovered (G : EventGraph Node Coord lo hi)
    (shape : ClassicalShape G) (samples : Finset Node) (c : Node) :
    decodeKind (degrees (G.toGARG samples).Topology c).1
      (degrees (G.toGARG samples).Topology c).2 = some (shape.kind c) := by
  rw [encoded_degrees, shape.arities]
  exact decode_kind_signature _

/-- A graph satisfying these binary conventions admits only one event-kind map. -/
theorem classical_kind_unique (G : EventGraph Node Coord lo hi)
    (a b : ClassicalShape G) : a.kind = b.kind := by
  funext c
  apply kind_signature_injective
  exact (a.arities c).symm.trans (b.arities c)

end
end WongEventDecoding
