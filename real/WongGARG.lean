import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Union
import SamuelAlexanderResearch.HistoryProjection

/-!
# Finite genome ARGs and their local ancestry

A finite interval presentation of the gARG definition in Wong et al. (2024),
Genetics 228, iyae100, p. 2 and Appendix E. Coordinates are linearly ordered;
node identifiers carry no time order. Edges are oriented ancestor to descendant,
the reverse of tracing an Appendix E parent pointer. The base structure does
not silently assume sample resolution, a unique local parent, or node dates.
-/

namespace WongGARG

open AncestryViews

universe u v

noncomputable section
local instance (α : Type*) : DecidableEq α := Classical.decEq α
local instance (P : Prop) : Decidable P := Classical.propDecidable P

structure Interval (Coord : Type v) [LinearOrder Coord] where
  lo : Coord
  hi : Coord
  proper : lo < hi

def Interval.Contains {Coord : Type v} [LinearOrder Coord]
    (I : Interval Coord) (x : Coord) : Prop := I.lo ≤ x ∧ x < I.hi

/-- Disjoint as half-open coordinate sets, permitting adjacent intervals. -/
def Interval.Disjoint {Coord : Type v} [LinearOrder Coord]
    (I J : Interval Coord) : Prop :=
  ∀ x, ¬ (I.Contains x ∧ J.Contains x)

structure EdgeRecord (Node : Type u) (Coord : Type v) [LinearOrder Coord] where
  parent : Node
  child : Node
  regions : Finset (Interval Coord)
  disjoint : ∀ I ∈ regions, ∀ J ∈ regions, I ≠ J → I.Disjoint J

def EdgeRecord.Covers {Node : Type u} {Coord : Type v} [LinearOrder Coord]
    (e : EdgeRecord Node Coord) (x : Coord) : Prop :=
  ∃ I ∈ e.regions, I.Contains x

def RecordTopology {Node : Type u} {Coord : Type v} [LinearOrder Coord]
    (records : Finset (EdgeRecord Node Coord)) (parent child : Node) : Prop :=
  ∃ e ∈ records, e.parent = parent ∧ e.child = child

/-- Finite nodes, designated samples, finitely represented disjoint genomic
intervals, and acyclicity. No node birthdates are required. -/
structure GARG (Node : Type u) (Coord : Type v) [Fintype Node] [LinearOrder Coord] where
  samples : Finset Node
  records : Finset (EdgeRecord Node Coord)
  acyclic : ∀ a, ¬ Reach (RecordTopology records) a a

namespace GARG
variable {Node : Type u} {Coord : Type v} [Fintype Node] [LinearOrder Coord]
variable (G : GARG Node Coord)

def Topology : Node → Node → Prop := RecordTopology G.records

def AtLocus (x : Coord) (parent child : Node) : Prop :=
  ∃ e ∈ G.records, e.parent = parent ∧ e.child = child ∧ e.Covers x

/-- A storage normalization condition, separately visible from graph semantics. -/
def CanonicalRecords : Prop :=
  ∀ e ∈ G.records, ∀ f ∈ G.records,
    e.parent = f.parent → e.child = f.child → e = f

/-- An optional well-formedness condition ruling out topological ghost edges. -/
def NonemptyAnnotations : Prop := ∀ e ∈ G.records, e.regions.Nonempty

/-- The biological single-parent premise needed to extract a local forest. -/
def UniqueParentAt (x : Coord) : Prop :=
  ∀ child a b, G.AtLocus x a child → G.AtLocus x b child → a = b

/-- Being at, or ancestral to, a sample at this one fixed coordinate. -/
def SampleAncestral (x : Coord) (a : Node) : Prop :=
  ∃ s ∈ G.samples, a = s ∨ Reach (G.AtLocus x) a s

/-- Appendix E extraction keeps precisely sample-ancestral local edges. -/
def ExtractedAt (x : Coord) (parent child : Node) : Prop :=
  G.AtLocus x parent child ∧ G.SampleAncestral x child

/-- Every annotated coordinate is ancestral to a designated sample. -/
def SampleSupported : Prop :=
  ∀ x a b, G.AtLocus x a b → G.SampleAncestral x b

theorem locus_edge_topology {x : Coord} {a b : Node}
    (h : G.AtLocus x a b) : G.Topology a b := by
  obtain ⟨e, he, ha, hb, _⟩ := h
  exact ⟨e, he, ha, hb⟩

theorem locus_path_topology {x : Coord} {a b : Node}
    (h : Reach (G.AtLocus x) a b) : Reach G.Topology a b :=
  reach_mono (fun _ _ he => G.locus_edge_topology he) h

theorem locus_acyclic (x : Coord) (a : Node) : ¬ Reach (G.AtLocus x) a a :=
  fun h => G.acyclic a (G.locus_path_topology h)

theorem topology_irreflexive (a : Node) : ¬ G.Topology a a :=
  fun h => G.acyclic a (.edge h)

theorem topology_iff_erased (hne : G.NonemptyAnnotations) (a b : Node) :
    G.Topology a b ↔ EraseIndex G.AtLocus a b := by
  constructor
  · rintro ⟨e, he, ha, hb⟩
    obtain ⟨I, hI⟩ := hne e he
    exact ⟨I.lo, e, he, ha, hb, I, hI, le_rfl, I.proper⟩
  · rintro ⟨x, hx⟩
    exact G.locus_edge_topology hx

theorem extracted_eq_local_iff_sampleSupported :
    (∀ x a b, G.ExtractedAt x a b ↔ G.AtLocus x a b) ↔ G.SampleSupported := by
  constructor
  · intro h x a b he
    exact ((h x a b).mpr he).2
  · intro h x a b
    exact ⟨And.left, fun he => ⟨he, h x a b he⟩⟩

theorem extracted_acyclic (x : Coord) (a : Node) :
    ¬ Reach (G.ExtractedAt x) a a := by
  intro h
  exact G.locus_acyclic x a (reach_mono (fun _ _ he => he.1) h)

/-- Parent pointers are deliberately partial: roots have value `none`. -/
def localParent (x : Coord) (child : Node) : Option Node :=
  if h : ∃ parent, G.AtLocus x parent child then some (Classical.choose h) else none

theorem localParent_eq_some_iff (x : Coord) (hunique : G.UniqueParentAt x)
    (child parent : Node) : G.localParent x child = some parent ↔ G.AtLocus x parent child := by
  classical
  unfold localParent
  split
  · rename_i h
    constructor
    · intro he
      have hp : Classical.choose h = parent := Option.some.inj he
      simpa only [hp] using Classical.choose_spec h
    · intro he
      exact congrArg some (hunique child _ parent (Classical.choose_spec h) he)
  · rename_i h
    constructor
    · intro he
      cases he
    · intro he
      exact False.elim (h ⟨parent, he⟩)

theorem localParent_none_iff (x : Coord) (child : Node) :
    G.localParent x child = none ↔ ∀ parent, ¬ G.AtLocus x parent child := by
  classical
  unfold localParent
  split
  · rename_i h
    constructor
    · intro he
      cases he
    · intro he
      exact False.elim (he _ (Classical.choose_spec h))
  · rename_i h
    constructor
    · intro _ parent hp
      exact h ⟨parent, hp⟩
    · intro _
      rfl

/-- Exact local oriented-forest representation, using Option rather than a
sentinel node identifier. Unique local inheritance is an explicit premise. -/
theorem local_parent_representation (x : Coord) (hunique : G.UniqueParentAt x) :
    (∀ a b, G.AtLocus x a b ↔ G.localParent x b = some a) ∧
    (∀ a, ¬ Reach (fun p c => G.localParent x c = some p) a a) := by
  refine ⟨fun a b => (G.localParent_eq_some_iff x hunique b a).symm, ?_⟩
  intro a h
  apply G.locus_acyclic x a
  exact reach_mono (fun p c he => (G.localParent_eq_some_iff x hunique c p).mp he) h

/-- Genome owners may coincide at cell-level steps. This is a conditional
pedigree projection, not an inference of biological owners from the graph. -/
theorem locus_path_projects {E : SpeciesBridge.Graph} (owner : Node → Nat)
    (sound : ∀ e ∈ G.records,
      HistoryProjection.SameOrDescendant E (owner e.parent) (owner e.child))
    {x : Coord} {a b : Node} (h : Reach (G.AtLocus x) a b) :
    HistoryProjection.SameOrDescendant E (owner a) (owner b) := by
  apply HistoryProjection.path_projects owner ?_ h
  intro p c he
  obtain ⟨e, member, hp, hc, _⟩ := he
  simpa only [hp, hc] using sound e member

end GARG

/-- In a relation with at most one incoming parent, two ancestors of the same
vertex lie on a single ordered ancestral chain. -/
theorem ancestors_comparable {Node : Type u} {R : Node → Node → Prop}
    (unique : ∀ c a b, R a c → R b c → a = b) {a b c : Node}
    (ha : Reach R a c) (hb : Reach R b c) :
    a = b ∨ Reach R a b ∨ Reach R b a := by
  induction ha generalizing b with
  | edge hac =>
    cases hb with
    | edge hbc => exact Or.inl (unique _ _ _ hac hbc)
    | snoc hbd hdc =>
      have eq := unique _ _ _ hac hdc
      subst_vars
      exact Or.inr (Or.inr hbd)
  | snoc had hdc ih =>
    cases hb with
    | edge hbc =>
      have eq := unique _ _ _ hdc hbc
      subst_vars
      exact Or.inr (Or.inl had)
    | snoc hbe hec =>
      have eq := unique _ _ _ hdc hec
      subst_vars
      exact ih hbe

namespace GARG
variable {Node : Type u} {Coord : Type v} [Fintype Node] [LinearOrder Coord]
variable (G : GARG Node Coord)

theorem local_ancestors_comparable (x : Coord) (hunique : G.UniqueParentAt x)
    {a b c : Node} (ha : Reach (G.AtLocus x) a c) (hb : Reach (G.AtLocus x) b c) :
    a = b ∨ Reach (G.AtLocus x) a b ∨ Reach (G.AtLocus x) b a :=
  ancestors_comparable hunique ha hb

end GARG

private theorem reach_trans {Node : Type u} {R : Node → Node → Prop}
    {a b c : Node} (hab : Reach R a b) (hbc : Reach R b c) : Reach R a c := by
  induction hbc with
  | edge he => exact .snoc hab he
  | snoc _ he ih => exact .snoc ih he

private theorem block_code_lt {k l i j n : Nat} (hi : i < n) (hkl : k < l) :
    k * n + i < l * n + j := by
  have hm : (k + 1) * n ≤ l * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hkl)
  have hb : k * n + i < (k + 1) * n := by
    simpa only [Nat.add_mul, Nat.one_mul] using Nat.add_lt_add_left hi (k * n)
  exact lt_of_lt_of_le hb (le_trans hm (Nat.le_add_right _ _))

namespace GARG
variable {Node : Type u} {Coord : Type v} [Fintype Node] [LinearOrder Coord]
variable (G : GARG Node Coord)

/-- Strict ancestors, computed classically from the finite topology. -/
def ancestorSet (v : Node) : Finset Node :=
  Finset.univ.filter (fun u => Reach G.Topology u v)

@[simp] theorem mem_ancestorSet (u v : Node) :
    u ∈ G.ancestorSet v ↔ Reach G.Topology u v := by
  simp only [ancestorSet, Finset.mem_filter, Finset.mem_univ, true_and]

theorem ancestor_count_lt_of_edge {a b : Node} (h : G.Topology a b) :
    (G.ancestorSet a).card < (G.ancestorSet b).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro u hu
    exact (G.mem_ancestorSet u b).mpr (.snoc ((G.mem_ancestorSet u a).mp hu) h)
  · intro heq
    have ha : a ∈ G.ancestorSet b := (G.mem_ancestorSet a b).mpr (.edge h)
    rw [← heq] at ha
    exact G.acyclic a ((G.mem_ancestorSet a a).mp ha)

theorem ancestor_count_lt_card (a : Node) : (G.ancestorSet a).card < Fintype.card Node := by
  have h : G.ancestorSet a ⊂ Finset.univ := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    intro heq
    have ha : a ∈ G.ancestorSet a := by rw [heq]; exact Finset.mem_univ _
    exact G.acyclic a ((G.mem_ancestorSet a a).mp ha)
  simpa only [Finset.card_univ] using Finset.card_lt_card h

/-- An injective topological numbering, derived from the DAG rather than
assumed of its identifiers. Gaps are permitted; the finite bound is n squared. -/
def orderCode (a : Node) : Nat :=
  (G.ancestorSet a).card * Fintype.card Node + (Fintype.equivFin Node a).val

theorem orderCode_edge {a b : Node} (h : G.Topology a b) : G.orderCode a < G.orderCode b :=
  block_code_lt (Fintype.equivFin Node a).isLt (G.ancestor_count_lt_of_edge h)

theorem orderCode_lt_bound (a : Node) :
    G.orderCode a < Fintype.card Node * Fintype.card Node := by
  have h := block_code_lt (j := 0) (Fintype.equivFin Node a).isLt
    (G.ancestor_count_lt_card a)
  simpa only [orderCode, Nat.add_zero] using h

theorem orderCode_injective : Function.Injective G.orderCode := by
  intro a b heq
  rcases lt_trichotomy (G.ancestorSet a).card (G.ancestorSet b).card with hlt | hsame | hgt
  · have hltCode : G.orderCode a < G.orderCode b :=
      block_code_lt (Fintype.equivFin Node a).isLt hlt
    exact False.elim ((Nat.ne_of_lt hltCode) heq)
  · unfold orderCode at heq
    rw [hsame] at heq
    exact (Fintype.equivFin Node).injective (Fin.ext (Nat.add_left_cancel heq))
  · have hgtCode : G.orderCode b < G.orderCode a :=
      block_code_lt (Fintype.equivFin Node b).isLt hgt
    exact False.elim ((Nat.ne_of_lt hgtCode) heq.symm)

/-- Every finite gARG has a bounded injective increasing embedding into the
natural-number vertex convention used by the Alexander interfaces. -/
theorem exists_finite_topological_numbering :
    ∃ (bound : Nat) (code : Node → Nat), Function.Injective code ∧
      (∀ a, code a < bound) ∧ (∀ a b, G.Topology a b → code a < code b) :=
  ⟨Fintype.card Node * Fintype.card Node, G.orderCode, G.orderCode_injective,
    G.orderCode_lt_bound, fun _ _ he => G.orderCode_edge he⟩

end GARG

namespace GARG
variable {Node : Type u} {Coord : Type v} [Fintype Node] [LinearOrder Coord]
variable (G : GARG Node Coord)

/-- The finitely many annotation endpoints at which local inheritance can change. -/
def breakpoints : Finset Coord :=
  G.records.biUnion (fun e => e.regions.biUnion (fun I => {I.lo, I.hi}))

theorem lo_mem_breakpoints {e : EdgeRecord Node Coord} (he : e ∈ G.records)
    {I : Interval Coord} (hI : I ∈ e.regions) : I.lo ∈ G.breakpoints := by
  apply Finset.mem_biUnion.mpr
  refine ⟨e, he, Finset.mem_biUnion.mpr ⟨I, hI, ?_⟩⟩
  simp

theorem hi_mem_breakpoints {e : EdgeRecord Node Coord} (he : e ∈ G.records)
    {I : Interval Coord} (hI : I ∈ e.regions) : I.hi ∈ G.breakpoints := by
  apply Finset.mem_biUnion.mpr
  refine ⟨e, he, Finset.mem_biUnion.mpr ⟨I, hI, ?_⟩⟩
  simp

/-- If no endpoint is crossed, a half-open interval cannot change membership.
The forbidden boundary region is (x,y], which handles endpoints exactly. -/
theorem interval_constant_without_breakpoint {x y : Coord} (hxy : x ≤ y)
    (hno : ∀ z ∈ G.breakpoints, ¬ (x < z ∧ z ≤ y))
    {e : EdgeRecord Node Coord} (he : e ∈ G.records)
    {I : Interval Coord} (hI : I ∈ e.regions) : I.Contains x ↔ I.Contains y := by
  constructor
  · intro hx
    refine ⟨le_trans hx.1 hxy, ?_⟩
    by_contra hy
    exact hno I.hi (G.hi_mem_breakpoints he hI) ⟨hx.2, le_of_not_gt hy⟩
  · intro hy
    refine ⟨?_, lt_of_le_of_lt hxy hy.2⟩
    by_contra hx
    exact hno I.lo (G.lo_mem_breakpoints he hI) ⟨lt_of_not_ge hx, hy.1⟩

theorem locus_constant_without_breakpoint {x y : Coord} (hxy : x ≤ y)
    (hno : ∀ z ∈ G.breakpoints, ¬ (x < z ∧ z ≤ y)) (a b : Node) :
    G.AtLocus x a b ↔ G.AtLocus y a b := by
  constructor
  · rintro ⟨e, he, ha, hb, I, hI, hx⟩
    exact ⟨e, he, ha, hb, I, hI,
      (G.interval_constant_without_breakpoint hxy hno he hI).mp hx⟩
  · rintro ⟨e, he, ha, hb, I, hI, hy⟩
    exact ⟨e, he, ha, hb, I, hI,
      (G.interval_constant_without_breakpoint hxy hno he hI).mpr hy⟩

/-- Piecewise constancy of ancestry, not a scale symmetry or graph self-similarity. -/
theorem ancestry_constant_without_breakpoint {x y : Coord} (hxy : x ≤ y)
    (hno : ∀ z ∈ G.breakpoints, ¬ (x < z ∧ z ≤ y)) (a b : Node) :
    Reach (G.AtLocus x) a b ↔ Reach (G.AtLocus y) a b := by
  constructor
  · exact reach_mono (fun u v he => (G.locus_constant_without_breakpoint hxy hno u v).mp he)
  · exact reach_mono (fun u v he => (G.locus_constant_without_breakpoint hxy hno u v).mpr he)

/-- Re-encoding only actual genome edges into the bounded natural-number prefix. -/
def natTopology (i j : Nat) : Prop :=
  ∃ a b, G.orderCode a = i ∧ G.orderCode b = j ∧ G.Topology a b

theorem natTopology_edge_order {i j : Nat} (h : G.natTopology i j) : i < j := by
  obtain ⟨a, b, ha, hb, hab⟩ := h
  simpa only [ha, hb] using G.orderCode_edge hab

theorem natTopology_edge_bounds {i j : Nat} (h : G.natTopology i j) :
    i < Fintype.card Node * Fintype.card Node ∧
    j < Fintype.card Node * Fintype.card Node := by
  obtain ⟨a, b, ha, hb, _⟩ := h
  constructor
  · simpa only [ha] using G.orderCode_lt_bound a
  · simpa only [hb] using G.orderCode_lt_bound b

theorem natTopology_path_lifts {i j : Nat} (h : Reach G.natTopology i j) :
    ∃ a b, G.orderCode a = i ∧ G.orderCode b = j ∧ Reach G.Topology a b := by
  induction h with
  | edge he =>
    obtain ⟨a, b, ha, hb, hab⟩ := he
    exact ⟨a, b, ha, hb, .edge hab⟩
  | snoc _ he ih =>
    obtain ⟨a, b, ha, hb, hab⟩ := ih
    obtain ⟨c, d, hc, hd, hcd⟩ := he
    have hbc : b = c := G.orderCode_injective (hb.trans hc.symm)
    subst c
    exact ⟨a, d, ha, hd, .snoc hab hcd⟩

/-- Exact ancestry reflection: unused natural identifiers create no extra paths. -/
theorem natTopology_path_iff (a b : Node) :
    Reach G.natTopology (G.orderCode a) (G.orderCode b) ↔ Reach G.Topology a b := by
  constructor
  · intro h
    obtain ⟨c, d, hc, hd, hcd⟩ := G.natTopology_path_lifts h
    have hca : c = a := G.orderCode_injective hc
    have hdb : d = b := G.orderCode_injective hd
    simpa only [hca, hdb] using hcd
  · intro h
    induction h with
    | edge he => exact .edge ⟨_, _, rfl, rfl, he⟩
    | snoc _ he ih => exact .snoc ih ⟨_, _, rfl, rfl, he⟩

end GARG
end
end WongGARG

#print axioms WongGARG.GARG.locus_path_topology
#print axioms WongGARG.GARG.locus_acyclic
#print axioms WongGARG.GARG.topology_iff_erased
#print axioms WongGARG.GARG.extracted_eq_local_iff_sampleSupported
#print axioms WongGARG.GARG.local_parent_representation
#print axioms WongGARG.GARG.local_ancestors_comparable
#print axioms WongGARG.GARG.locus_path_projects

#print axioms WongGARG.GARG.exists_finite_topological_numbering


#print axioms WongGARG.GARG.ancestry_constant_without_breakpoint
#print axioms WongGARG.GARG.natTopology_path_iff


