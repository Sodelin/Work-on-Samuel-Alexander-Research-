import Std

/-!
# The specieslike-cluster bridge for the binary `P_s` geometry

The vertices are natural numbers. The edge relation is independent of the
binary word `s`: `u -> w` iff `2 <= w` and `w = u + 1` or `w = u + 2`.
In particular there is NO edge from 0 to 1. This file proves the graph
geometry; it does not formalize the word labels or eventual-periodicity
classification.

Species predicates follow Alexander (2026), arXiv:2602.05274v1,
Definitions 2-4, 8-9. Ancestorhood is strict. Connectivity is weak
connectivity in the induced subgraph. Finite sets are represented by finite
list covers, with their equivalence to boundedness on Nat proved below.
-/

namespace SpeciesBridge

abbrev NatSet := Nat -> Prop
abbrev Graph := Nat -> Nat -> Prop

/-- Standard finiteness as containment in the entries of a finite list. -/
def FiniteSupport (S : NatSet) : Prop :=
  exists xs : List Nat, forall n, S n -> n ∈ xs

def BoundedSupport (S : NatSet) : Prop :=
  exists bound : Nat, forall n, S n -> n < bound

def InfiniteSupport (S : NatSet) : Prop := ¬ FiniteSupport S

private theorem member_le_sum {xs : List Nat} {n : Nat}
    (h : n ∈ xs) : n <= xs.sum := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.mem_cons] at h
    simp only [List.sum_cons]
    rcases h with h | h
    · subst n; omega
    · have := ih h; omega

/-- The finite-support encoding is exactly boundedness on natural numbers. -/
theorem finiteSupport_iff_bounded (S : NatSet) :
    FiniteSupport S ↔ BoundedSupport S := by
  constructor
  · rintro ⟨xs, hxs⟩
    refine ⟨xs.sum + 1, ?_⟩
    intro n hn
    have := member_le_sum (hxs n hn)
    omega
  · rintro ⟨bound, hbound⟩
    refine ⟨List.range bound, ?_⟩
    intro n hn
    exact List.mem_range.mpr (hbound n hn)

theorem finiteSupport_mono {S T : NatSet}
    (hST : forall n, S n -> T n) (hT : FiniteSupport T) :
    FiniteSupport S := by
  obtain ⟨xs, hxs⟩ := hT
  exact ⟨xs, fun n hn => hxs n (hST n hn)⟩

/-- Nonempty directed paths; there is no reflexivity constructor. -/
inductive Descendant (E : Graph) : Nat -> Nat -> Prop where
  | edge {u v : Nat} : E u v -> Descendant E u v
  | snoc {u v w : Nat} :
      Descendant E u v -> E v w -> Descendant E u w

theorem Descendant.trans {E : Graph} {u v w : Nat}
    (huv : Descendant E u v) (hvw : Descendant E v w) :
    Descendant E u w := by
  induction hvw with
  | edge h => exact .snoc huv h
  | snoc _ h ih => exact .snoc ih h

/-- The binary `P_s` graph after forgetting edge labels. -/
def PsEdge (u w : Nat) : Prop :=
  2 <= w ∧ (w = u + 1 ∨ w = u + 2)

theorem psEdge_strict {u w : Nat} (h : PsEdge u w) : u < w := by
  rcases h with ⟨_, h | h⟩ <;> omega

theorem no_edge_zero_one : ¬ PsEdge 0 1 := by
  intro h
  have := h.1
  omega

theorem psDescendant_strict {u w : Nat}
    (h : Descendant PsEdge u w) : u < w := by
  induction h with
  | edge h => exact psEdge_strict h
  | snoc _ h ih => have := psEdge_strict h; omega

theorem psDescendant_destination {u w : Nat}
    (h : Descendant PsEdge u w) : 2 <= w := by
  cases h with
  | edge h => exact h.1
  | snoc _ h => exact h.1

/-- Every positive vertex reaches every strictly larger vertex. -/
theorem positive_reaches {u w : Nat} (hu : 1 <= u) (huw : u < w) :
    Descendant PsEdge u w := by
  induction w with
  | zero => omega
  | succ w ih =>
    by_cases hwu : w = u
    · subst w
      apply Descendant.edge
      exact ⟨by omega, Or.inl rfl⟩
    · have huw' : u < w := by omega
      apply Descendant.snoc (ih huw')
      exact ⟨by omega, Or.inl rfl⟩

/-- Root 0 reaches precisely the vertices from 2 onward. -/
theorem zero_reaches {w : Nat} (hw : 2 <= w) :
    Descendant PsEdge 0 w := by
  have h02 : Descendant PsEdge 0 2 :=
    .edge ⟨by omega, Or.inr rfl⟩
  by_cases hw2 : w = 2
  · simpa [hw2] using h02
  · exact h02.trans (positive_reaches (by omega) (by omega))

/-- Complete reachability characterization for the actual binary graph. -/
theorem psDescendant_iff (u w : Nat) :
    Descendant PsEdge u w ↔ u < w ∧ 2 <= w := by
  constructor
  · intro h
    exact ⟨psDescendant_strict h, psDescendant_destination h⟩
  · rintro ⟨huw, hw⟩
    by_cases hu : u = 0
    · subst u; exact zero_reaches hw
    · exact positive_reaches (by omega) huw

theorem psNonDescendant_iff (u w : Nat) :
    ¬ Descendant PsEdge u w ↔ w <= u ∨ w <= 1 := by
  rw [psDescendant_iff]
  omega

/-- An explicit finite initial segment covers each vertex's non-descendants. -/
theorem psNonDescendant_bound {u w : Nat}
    (h : ¬ Descendant PsEdge u w) : w < u + 2 := by
  have := (psNonDescendant_iff u w).mp h
  omega

theorem psNonDescendants_finite (u : Nat) :
    FiniteSupport (fun w => ¬ Descendant PsEdge u w) := by
  apply (finiteSupport_iff_bounded _).mpr
  exact ⟨u + 2, fun _ h => psNonDescendant_bound h⟩

/-- Reflexive undirected reachability using only vertices in the set. -/
inductive WeakReach (E : Graph) (S : NatSet) : Nat -> Nat -> Prop where
  | refl {u : Nat} : S u -> WeakReach E S u u
  | edge {u v : Nat} : S u -> S v ->
      (E u v ∨ E v u) -> WeakReach E S u v
  | trans {u v w : Nat} :
      WeakReach E S u v -> WeakReach E S v w -> WeakReach E S u w

theorem WeakReach.symm {E : Graph} {S : NatSet} {u v : Nat}
    (h : WeakReach E S u v) : WeakReach E S v u := by
  induction h with
  | refl hu => exact .refl hu
  | edge hu hv huv => exact .edge hv hu huv.symm
  | trans _ _ huv hvw => exact .trans hvw huv

def Whole : NatSet := fun _ => True

theorem Descendant.weakReach_whole {E : Graph} {u w : Nat}
    (h : Descendant E u w) : WeakReach E Whole u w := by
  induction h with
  | edge h => exact .edge trivial trivial (Or.inl h)
  | snoc _ h ih => exact .trans ih (.edge trivial trivial (Or.inl h))

def WeaklyConnected (E : Graph) (S : NatSet) : Prop :=
  (exists u, S u) ∧ forall u v, S u -> S v -> WeakReach E S u v

/-- Definition 2: finitely many descendants or finitely many non-descendants. -/
def IAP (E : Graph) (S : NatSet) : Prop :=
  forall v, S v ->
    FiniteSupport (fun w => S w ∧ Descendant E v w) ∨
    FiniteSupport (fun w => S w ∧ ¬ Descendant E v w)

/-- Definition 3, using ancestorhood in the ambient graph. -/
def Convex (E : Graph) (S : NatSet) : Prop :=
  forall v, (exists a, S a ∧ Descendant E a v) ->
    (exists d, S d ∧ Descendant E v d) -> S v

/-- Definition 4. -/
def Specieslike (E : Graph) (S : NatSet) : Prop :=
  WeaklyConnected E S ∧ IAP E S ∧ Convex E S

/-- Definition 8: one member is ancestor of every other member. -/
def CommonAncestor (E : Graph) (S : NatSet) : Prop :=
  exists v, S v ∧ forall w, S w -> w ≠ v -> Descendant E v w

/-- Definition 9: infinitude is global in the premise and internal in conclusion. -/
def Reflection (E : Graph) (S : NatSet) : Prop :=
  forall v, S v -> InfiniteSupport (Descendant E v) ->
    InfiniteSupport (fun w => S w ∧ Descendant E v w)

/-- Inclusion-maximality among specieslike subsets of this same ambient graph. -/
def MaximalSpecieslike (E : Graph) (S : NatSet) : Prop :=
  Specieslike E S ∧ forall T : NatSet,
    (forall v, S v -> T v) -> Specieslike E T -> forall v, T v -> S v

theorem psWhole_weaklyConnected : WeaklyConnected PsEdge Whole := by
  refine ⟨⟨0, trivial⟩, ?_⟩
  intro u v _ _
  have hu : Descendant PsEdge u (u + v + 2) :=
    (psDescendant_iff _ _).mpr ⟨by omega, by omega⟩
  have hv : Descendant PsEdge v (u + v + 2) :=
    (psDescendant_iff _ _).mpr ⟨by omega, by omega⟩
  exact .trans hu.weakReach_whole hv.weakReach_whole.symm

/-- In fact every subset has IAP, since non-descendants are globally finite. -/
theorem psSubset_iap (S : NatSet) : IAP PsEdge S := by
  intro v _
  exact Or.inr (finiteSupport_mono (fun _ h => h.2) (psNonDescendants_finite v))

theorem whole_convex (E : Graph) : Convex E Whole := by
  intro _ _ _; trivial

theorem whole_reflection (E : Graph) : Reflection E Whole := by
  intro v _ hinf hfin
  apply hinf
  exact finiteSupport_mono (fun _ h => ⟨trivial, h⟩) hfin

theorem psWhole_specieslike : Specieslike PsEdge Whole :=
  ⟨psWhole_weaklyConnected, psSubset_iap Whole, whole_convex PsEdge⟩

theorem psSubset_specieslike_iff (S : NatSet) :
    Specieslike PsEdge S ↔ WeaklyConnected PsEdge S ∧ Convex PsEdge S := by
  constructor
  · intro h; exact ⟨h.1, h.2.2⟩
  · intro h; exact ⟨h.1, psSubset_iap S, h.2⟩

theorem psWhole_maximalSpecieslike : MaximalSpecieslike PsEdge Whole := by
  refine ⟨psWhole_specieslike, ?_⟩
  intro _ _ _ _ _
  trivial

def Root (E : Graph) (v : Nat) : Prop := forall u, ¬ E u v

/-- The two initial vertices, and only those vertices, have no parents. -/
theorem psRoot_iff (v : Nat) : Root PsEdge v ↔ v = 0 ∨ v = 1 := by
  constructor
  · intro h
    by_cases hv : 2 <= v
    · have he : PsEdge (v - 1) v := ⟨hv, Or.inl (by omega)⟩
      exact False.elim (h (v - 1) he)
    · omega
  · intro hv u he
    have hdest := he.1
    omega

theorem no_psDescendant_zero (u : Nat) : ¬ Descendant PsEdge u 0 := by
  intro h
  have := psDescendant_destination h
  omega

theorem no_psDescendant_one (u : Nat) : ¬ Descendant PsEdge u 1 := by
  intro h
  have := psDescendant_destination h
  omega

/-- The full graph fails CA: neither root can descend from any other vertex. -/
theorem psWhole_not_commonAncestor : ¬ CommonAncestor PsEdge Whole := by
  rintro ⟨v, _, hv⟩
  by_cases h0 : v = 0
  · subst v
    exact no_psDescendant_one 0 (hv 1 trivial (by omega))
  · exact no_psDescendant_zero v (hv 0 trivial (by omega))

theorem whole_infinite : InfiniteSupport Whole := by
  intro hfin
  obtain ⟨bound, hbound⟩ := (finiteSupport_iff_bounded Whole).mp hfin
  have := hbound bound trivial
  omega

theorem psDescendants_infinite (v : Nat) :
    InfiniteSupport (Descendant PsEdge v) := by
  intro hfin
  obtain ⟨bound, hbound⟩ := (finiteSupport_iff_bounded _).mp hfin
  have hd : Descendant PsEdge v (v + bound + 2) :=
    (psDescendant_iff _ _).mpr ⟨by omega, by omega⟩
  have := hbound _ hd
  omega

theorem psChildren_finite (v : Nat) : FiniteSupport (PsEdge v) := by
  refine ⟨[v + 1, v + 2], ?_⟩
  intro w hw
  rcases hw.2 with h | h <;> simp [h]

theorem finite_birthdate_prefix (date : Nat) :
    FiniteSupport (fun v => v < date) :=
  (finiteSupport_iff_bounded _).mpr ⟨date, fun _ h => h⟩

/-- The natural-date counterpart of Definition 1, with birthdate `t(v) = v`.

The source quantifies over real date bounds. This Std-only package quantifies
over natural bounds. Passing from natural bounds to real bounds uses the
Archimedean embedding of Nat in Real, which is not formalized in this file.
-/
def NaturalDateBiosphere (E : Graph) : Prop :=
  (forall u w, E u w -> u < w) ∧
  (forall date, FiniteSupport (fun v => v < date)) ∧
  (forall v, FiniteSupport (E v)) ∧ InfiniteSupport Whole

theorem psNaturalDateBiosphere : NaturalDateBiosphere PsEdge :=
  ⟨fun _ _ h => psEdge_strict h, finite_birthdate_prefix,
    psChildren_finite, whole_infinite⟩

/-- Complete unconditional graph-geometry endpoint. No label/classification
premise and no common-ancestor premise occur in this theorem. -/
theorem psWhole_bridge :
    NaturalDateBiosphere PsEdge ∧
    MaximalSpecieslike PsEdge Whole ∧
    Reflection PsEdge Whole ∧
    ¬ CommonAncestor PsEdge Whole :=
  ⟨psNaturalDateBiosphere, psWhole_maximalSpecieslike,
    whole_reflection PsEdge, psWhole_not_commonAncestor⟩

/-- Every vertex of this particular graph inhabits a maximal specieslike
cluster satisfying REF. This is not a theorem about arbitrary biospheres. -/
theorem psEvery_vertex_in_maximal_cluster (v : Nat) :
    exists S : NatSet, S v ∧ MaximalSpecieslike PsEdge S ∧ Reflection PsEdge S :=
  ⟨Whole, trivial, psWhole_maximalSpecieslike, whole_reflection PsEdge⟩

end SpeciesBridge

#print axioms SpeciesBridge.finiteSupport_iff_bounded
#print axioms SpeciesBridge.psDescendant_iff
#print axioms SpeciesBridge.psWhole_specieslike
#print axioms SpeciesBridge.psWhole_maximalSpecieslike
#print axioms SpeciesBridge.psWhole_not_commonAncestor
#print axioms SpeciesBridge.psDescendants_infinite
#print axioms SpeciesBridge.psRoot_iff
#print axioms SpeciesBridge.psNaturalDateBiosphere
#print axioms SpeciesBridge.psWhole_bridge
#print axioms SpeciesBridge.psEvery_vertex_in_maximal_cluster
