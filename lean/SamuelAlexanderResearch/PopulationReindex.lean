import SamuelAlexanderResearch.BirthOrder
import SamuelAlexanderResearch.GeneralRootObstruction

/-!
# Arbitrary-presentation population transport

An infinite vertex type with locally finite ordered birth times is enumerated
using `BirthOrder`. Functional labelled edges, actual parentless roots, and
bounded child-cover lists then produce an actual `InfiniteLabeledPopulation`.
Neither an enumeration nor an aggregate degree inequality is an input.
-/

namespace PopulationReindex

open BirthOrder PopulationCounting

universe u v

def NoParents {V : Type u} (edge : V → V → Option Nat) (x : V) : Prop :=
  ∀ parent, edge parent x = none

/-- A population in its original vertex and time presentation. Finite covers
are ordinary finite-list covers, and the child cap bounds their actual length. -/
structure PresentedPopulation {V : Type u} {Time : Type v} [LE Time] [LT Time]
    (birth : V → Time) (k d : Nat) where
  infinite : InfiniteVertices V
  finite_sublevels : FiniteSublevels birth
  edge : V → V → Option Nat
  birth_order : ∀ x y, (edge x y).isSome = true → birth x < birth y
  label_valid : ∀ x y label, edge x y = some label → label < k
  roots_finite : FiniteCover (NoParents edge)
  parent_of_label : ∀ y, ¬ NoParents edge y →
    ∀ label, label < k → ∃ x, edge x y = some label
  children : ∀ x, ∃ ys : List V, ys.length ≤ d ∧
    ∀ y, (edge x y).isSome = true → y ∈ ys

theorem sumBelow_indicator_eq_filter_length (f : Nat → Bool) (n : Nat) :
    sumBelow n (fun i => if f i then 1 else 0) = ((List.range n).filter f).length := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sumBelow_succ, List.range_succ, List.filter_append, List.length_append, ← ih]
    cases hf : f n <;> simp [hf]

/-- Counting distinct entries in a natural prefix is bounded by any covering
list, even if that list contains duplicates or extra vertices. -/
theorem sumBelow_indicator_le_cover (f : Nat → Bool) (n : Nat) (xs : List Nat)
    (hcover : ∀ i, i < n → f i = true → i ∈ xs) :
    sumBelow n (fun i => if f i then 1 else 0) ≤ xs.length := by
  rw [sumBelow_indicator_eq_filter_length]
  have hnodup : ((List.range n).filter f).Nodup := List.Pairwise.filter f List.nodup_range
  apply hnodup.length_le_of_subset
  intro i hi
  obtain ⟨hirange, hfi⟩ := List.mem_filter.mp hi
  exact hcover i (List.mem_range.mp hirange) hfi

variable {V : Type u} {Time : Type v} [LE Time] [LT Time]
variable [Std.IsLinearPreorder Time]
variable {birth : V → Time} {k d : Nat}

noncomputable def enumeration (p : PresentedPopulation birth k d) : OrderedEnumeration birth :=
  orderedEnumeration birth p.infinite p.finite_sublevels

noncomputable def indexedEdge (p : PresentedPopulation birth k d) (i j : Nat) : Option Nat :=
  p.edge ((enumeration p).toFun i) ((enumeration p).toFun j)

noncomputable def indexedRoot (p : PresentedPopulation birth k d) (i : Nat) : Bool := by
  classical
  exact decide (NoParents p.edge ((enumeration p).toFun i))

theorem indexedRoot_true_iff (p : PresentedPopulation birth k d) (i : Nat) :
    indexedRoot p i = true ↔ NoParents p.edge ((enumeration p).toFun i) := by
  classical
  simp [indexedRoot]

theorem indexedRoot_false_iff (p : PresentedPopulation birth k d) (i : Nat) :
    indexedRoot p i = false ↔ ¬ NoParents p.edge ((enumeration p).toFun i) := by
  classical
  simp [indexedRoot]

/-- Roothood is preserved in both directions, using surjectivity of the
constructed enumeration to cover every possible original parent. -/
theorem indexedRoot_noParents_iff (p : PresentedPopulation birth k d) (i : Nat) :
    indexedRoot p i = true ↔ ∀ j, indexedEdge p j i = none := by
  rw [indexedRoot_true_iff]
  constructor
  · intro hroot j
    exact hroot ((enumeration p).toFun j)
  · intro hroot x
    obtain ⟨j, rfl⟩ := (enumeration p).surjective x
    exact hroot j

theorem indexed_birth_order [Std.LawfulOrderLT Time]
    (p : PresentedPopulation birth k d) (i j : Nat)
    (he : (indexedEdge p i j).isSome = true) : i < j :=
  (enumeration p).edges_increase (fun x y => (p.edge x y).isSome = true)
    p.birth_order i j he

theorem indexed_label_valid (p : PresentedPopulation birth k d) (i j label : Nat)
    (he : indexedEdge p i j = some label) : label < k :=
  p.label_valid _ _ _ he

/-- Transport of the original child lists preserves their length bound. -/
theorem indexed_child_cover (p : PresentedPopulation birth k d) (i : Nat) :
    ∃ xs : List Nat, xs.length ≤ d ∧
      ∀ j, (indexedEdge p i j).isSome = true → j ∈ xs := by
  obtain ⟨ys, hlength, hys⟩ := p.children ((enumeration p).toFun i)
  refine ⟨ys.map (enumeration p).index, by simpa only [List.length_map] using hlength, ?_⟩
  exact (enumeration p).pullback_cover
    (fun y => (p.edge ((enumeration p).toFun i) y).isSome = true) ys hys

theorem indexed_child_bound_exists (p : PresentedPopulation birth k d) (i : Nat) :
    ∃ bound, ∀ j, (indexedEdge p i j).isSome = true → j < bound := by
  obtain ⟨xs, _, hxs⟩ := indexed_child_cover p i
  exact (SpeciesBridge.finiteSupport_iff_bounded _).mp ⟨xs, hxs⟩

noncomputable def childSupport (p : PresentedPopulation birth k d) (i : Nat) : Nat :=
  Classical.choose (indexed_child_bound_exists p i)

theorem childSupport_spec (p : PresentedPopulation birth k d) (i j : Nat)
    (he : (indexedEdge p i j).isSome = true) : j < childSupport p i :=
  Classical.choose_spec (indexed_child_bound_exists p i) j he

theorem indexed_child_cap (p : PresentedPopulation birth k d) (i : Nat) :
    sumBelow (childSupport p i) (fun j => edgeBit (indexedEdge p i j)) ≤ d := by
  obtain ⟨xs, hlength, hxs⟩ := indexed_child_cover p i
  exact Nat.le_trans
    (sumBelow_indicator_le_cover (fun j => (indexedEdge p i j).isSome)
      (childSupport p i) xs (fun j _ he => hxs j he)) hlength

theorem indexed_root_bound_exists (p : PresentedPopulation birth k d) :
    ∃ bound, ∀ i, indexedRoot p i = true → i < bound := by
  obtain ⟨bound, hbound⟩ := (enumeration p).finiteCover_pullback_bound (NoParents p.edge) p.roots_finite
  exact ⟨bound, fun i hi => hbound i ((indexedRoot_true_iff p i).mp hi)⟩

noncomputable def rootSupport (p : PresentedPopulation birth k d) : Nat :=
  Classical.choose (indexed_root_bound_exists p)

theorem rootSupport_spec (p : PresentedPopulation birth k d) (i : Nat)
    (hr : indexedRoot p i = true) : i < rootSupport p :=
  Classical.choose_spec (indexed_root_bound_exists p) i hr

variable [Std.LawfulOrderLT Time]

/-- The actual naturally indexed infinite population, constructed entirely
from the original local graph and finite-cover data. -/
noncomputable def toNatPopulation (p : PresentedPopulation birth k d) :
    InfiniteLabeledPopulation k d where
  edge := indexedEdge p
  root := indexedRoot p
  birth_order := indexed_birth_order p
  root_no_parents := fun i hi => (indexedRoot_noParents_iff p i).mp hi
  parent_of_label := by
    intro j hj label hl
    obtain ⟨x, hx⟩ := p.parent_of_label ((enumeration p).toFun j)
      ((indexedRoot_false_iff p j).mp hj) label hl
    obtain ⟨i, hi⟩ := (enumeration p).surjective x
    refine ⟨i, ?_⟩
    change p.edge ((enumeration p).toFun i) ((enumeration p).toFun j) = some label
    simpa only [hi] using hx
  childSupport := childSupport p
  no_children_after := by
    intro i j hj
    cases he : indexedEdge p i j with
    | none => rfl
    | some label =>
      have := childSupport_spec p i j (by simp [he])
      omega
  child_cap := indexed_child_cap p
  rootSupport := rootSupport p
  no_roots_after := by
    intro i hi
    cases hr : indexedRoot p i with
    | false => rfl
    | true =>
      have := rootSupport_spec p i hr
      omega

theorem toNatPopulation_edge (p : PresentedPopulation birth k d) (i j : Nat) :
    (toNatPopulation p).edge i j = p.edge ((enumeration p).toFun i) ((enumeration p).toFun j) := rfl

theorem toNatPopulation_root_iff (p : PresentedPopulation birth k d) (i : Nat) :
    (toNatPopulation p).root i = true ↔ NoParents p.edge ((enumeration p).toFun i) :=
  indexedRoot_true_iff p i

/-- Subcritical impossibility holds in the original arbitrary presentation. -/
theorem subcritical_impossible (p : PresentedPopulation birth k d) (hdk : d < k) : False :=
  infinite_subcritical_impossible (toNatPopulation p) hdk

theorem initial_vertices_are_roots (p : PresentedPopulation birth k d)
    (i : Nat) (hi : i < k) : NoParents p.edge ((enumeration p).toFun i) :=
  (toNatPopulation_root_iff p i).mp
    (GeneralRootObstruction.initial_declared_root (toNatPopulation p) i hi)

/-- At least `k` distinct roots in the original vertex type, expressed as
an injective family indexed by `Fin k`. -/
theorem at_least_k_distinct_roots (p : PresentedPopulation birth k d) :
    ∃ roots : Fin k → V, (∀ i, NoParents p.edge (roots i)) ∧
      ∀ i j, roots i = roots j → i = j := by
  refine ⟨fun i => (enumeration p).toFun i.val, ?_, ?_⟩
  · intro i
    exact initial_vertices_are_roots p i.val i.isLt
  · intro i j heq
    apply Fin.ext
    exact (enumeration p).injective i.val j.val heq

/-- Every finite cover of the original root set has at least `k` entries. -/
theorem alphabet_le_root_cover_length (p : PresentedPopulation birth k d) (roots : List V)
    (hcover : ∀ x, NoParents p.edge x → x ∈ roots) : k ≤ roots.length := by
  have hcount : sumBelow k (fun i => if indexedRoot p i then 1 else 0) = k := by
    calc
      _ = sumBelow k (fun _ => 1) := by
        apply sumBelow_congr
        intro i hi
        have hr := (indexedRoot_true_iff p i).mpr (initial_vertices_are_roots p i hi)
        simp only [hr, ↓reduceIte]
      _ = k := by simp
  have hbound := sumBelow_indicator_le_cover (indexedRoot p) k
    (roots.map (enumeration p).index) (by
      intro i _ hi
      exact (enumeration p).pullback_cover (NoParents p.edge) roots hcover i
        ((indexedRoot_true_iff p i).mp hi))
  simpa only [List.length_map, hcount] using hbound

end PopulationReindex

#print axioms PopulationReindex.enumeration
#print axioms PopulationReindex.sumBelow_indicator_le_cover
#print axioms PopulationReindex.indexedRoot_noParents_iff
#print axioms PopulationReindex.indexed_child_cap
#print axioms PopulationReindex.toNatPopulation
#print axioms PopulationReindex.toNatPopulation_root_iff
#print axioms PopulationReindex.subcritical_impossible
#print axioms PopulationReindex.at_least_k_distinct_roots
#print axioms PopulationReindex.alphabet_le_root_cover_length
