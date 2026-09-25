import SamuelAlexanderResearch.SpeciesBridge

/-!
# The two maximal IAP + convex + CA + REF sets in the binary graph

For the exact `PsEdge` relation, the two maximal sets satisfying all four
Alexander (2026) predicates are `C0 = {0} union {v | 2 <= v}` and
`C1 = {v | 1 <= v}`. They are also specieslike clusters. The whole graph is
specieslike and satisfies REF, but fails CA; thus its maximality concerns a
different class from the maximality proved here.

This is a classification inside this particular ambient graph, not a result
about arbitrary biospheres or the fixed-vertex-gender copy construction.
-/

namespace SpeciesCones

open SpeciesBridge

/-- A vertex together with all its strict descendants. -/
def Cone (root : Nat) : NatSet :=
  fun v => v = root ∨ Descendant PsEdge root v

abbrev C0 : NatSet := Cone 0
abbrev C1 : NatSet := Cone 1

theorem c0_iff (v : Nat) : C0 v ↔ v = 0 ∨ 2 <= v := by
  change (v = 0 ∨ Descendant PsEdge 0 v) ↔ _
  rw [psDescendant_iff]
  omega

theorem c1_iff (v : Nat) : C1 v ↔ 1 <= v := by
  change (v = 1 ∨ Descendant PsEdge 1 v) ↔ _
  rw [psDescendant_iff]
  omega

theorem cone_closed_under_descendants (root v w : Nat)
    (hv : Cone root v) (hvw : Descendant PsEdge v w) : Cone root w := by
  apply Or.inr
  rcases hv with h | h
  · subst v; exact hvw
  · exact h.trans hvw

theorem cone_commonAncestor (root : Nat) : CommonAncestor PsEdge (Cone root) := by
  refine ⟨root, Or.inl rfl, ?_⟩
  intro w hw hne
  rcases hw with h | h
  · exact False.elim (hne h)
  · exact h

theorem cone_convex (root : Nat) : Convex PsEdge (Cone root) := by
  intro v hancestor _
  obtain ⟨a, ha, hav⟩ := hancestor
  exact cone_closed_under_descendants root a v ha hav

theorem cone_reflection (root : Nat) : Reflection PsEdge (Cone root) := by
  intro v hv hinfinite hfinite
  apply hinfinite
  apply finiteSupport_mono _ hfinite
  intro w hw
  exact ⟨cone_closed_under_descendants root v w hv hw, hw⟩

private theorem descendant_weakReach_in_cone {root v : Nat}
    (h : Descendant PsEdge root v) : WeakReach PsEdge (Cone root) root v := by
  induction h with
  | edge h =>
    exact .edge (Or.inl rfl) (Or.inr (.edge h)) (Or.inl h)
  | snoc h hlast ih =>
    exact .trans ih (.edge (Or.inr h) (Or.inr (.snoc h hlast)) (Or.inl hlast))

theorem cone_weaklyConnected (root : Nat) : WeaklyConnected PsEdge (Cone root) := by
  refine ⟨⟨root, Or.inl rfl⟩, ?_⟩
  have fromRoot : forall v, Cone root v -> WeakReach PsEdge (Cone root) root v := by
    intro v hv
    rcases hv with h | h
    · subst v; exact .refl (Or.inl rfl)
    · exact descendant_weakReach_in_cone h
  intro u v hu hv
  exact .trans (fromRoot u hu).symm (fromRoot v hv)

theorem cone_specieslike (root : Nat) : Specieslike PsEdge (Cone root) :=
  ⟨cone_weaklyConnected root, psSubset_iap (Cone root), cone_convex root⟩

/-- The four predicates are imposed in the fixed ambient `PsEdge` graph. -/
def FourAxioms (S : NatSet) : Prop :=
  IAP PsEdge S ∧ Convex PsEdge S ∧ CommonAncestor PsEdge S ∧ Reflection PsEdge S

def MaximalFourAxioms (S : NatSet) : Prop :=
  FourAxioms S ∧ forall T : NatSet,
    (forall v, S v -> T v) -> FourAxioms T -> forall v, T v -> S v

theorem cone_fourAxioms (root : Nat) : FourAxioms (Cone root) :=
  ⟨psSubset_iap (Cone root), cone_convex root,
    cone_commonAncestor root, cone_reflection root⟩

/-- CA alone puts any set inside one of the two root cones. -/
theorem commonAncestor_subset_root_cone (S : NatSet)
    (hCA : CommonAncestor PsEdge S) :
    (forall v, S v -> C0 v) ∨ (forall v, S v -> C1 v) := by
  obtain ⟨a, _, hancestor⟩ := hCA
  by_cases ha : a = 0
  · subst a
    apply Or.inl
    intro v hv
    by_cases h0 : v = 0
    · exact Or.inl h0
    · exact Or.inr (hancestor v hv h0)
  · apply Or.inr
    intro v hv
    apply (c1_iff v).mpr
    by_cases hva : v = a
    · omega
    · have hlt := psDescendant_strict (hancestor v hv hva)
      omega

theorem c0_maximalFourAxioms : MaximalFourAxioms C0 := by
  refine ⟨cone_fourAxioms 0, ?_⟩
  intro T hsub hT
  rcases commonAncestor_subset_root_cone T hT.2.2.1 with h0 | h1
  · exact h0
  · have hbad : C1 0 := h1 0 (hsub 0 (Or.inl rfl))
    have hn := (c1_iff 0).mp hbad
    have hfalse : False := by omega
    exact False.elim hfalse

theorem c1_maximalFourAxioms : MaximalFourAxioms C1 := by
  refine ⟨cone_fourAxioms 1, ?_⟩
  intro T hsub hT
  rcases commonAncestor_subset_root_cone T hT.2.2.1 with h0 | h1
  · have hbad : C0 1 := h0 1 (hsub 1 (Or.inl rfl))
    have hn := (c0_iff 1).mp hbad
    have hfalse : False := by omega
    exact False.elim hfalse
  · exact h1

/-- Exact classification of the inclusion-maximal four-predicate sets. -/
theorem maximalFourAxioms_iff (S : NatSet) :
    MaximalFourAxioms S ↔ S = C0 ∨ S = C1 := by
  constructor
  · intro hS
    rcases commonAncestor_subset_root_cone S hS.1.2.2.1 with h0 | h1
    · apply Or.inl
      have hrev := hS.2 C0 h0 (cone_fourAxioms 0)
      funext v
      exact propext ⟨h0 v, hrev v⟩
    · apply Or.inr
      have hrev := hS.2 C1 h1 (cone_fourAxioms 1)
      funext v
      exact propext ⟨h1 v, hrev v⟩
  · rintro (rfl | rfl)
    · exact c0_maximalFourAxioms
    · exact c1_maximalFourAxioms

theorem c0_ne_c1 : C0 ≠ C1 := by
  intro heq
  have h0 : C0 0 := Or.inl rfl
  rw [heq] at h0
  have := (c1_iff 0).mp h0
  omega

theorem maximalFourAxioms_specieslike (S : NatSet)
    (h : MaximalFourAxioms S) : Specieslike PsEdge S := by
  rcases (maximalFourAxioms_iff S).mp h with rfl | rfl
  · exact cone_specieslike 0
  · exact cone_specieslike 1

/-- Every vertex lies in at least one of the two maximal constrained clusters. -/
theorem every_vertex_in_maximal_four_cluster (v : Nat) :
    exists S : NatSet, S v ∧ MaximalFourAxioms S ∧ Specieslike PsEdge S := by
  by_cases hv : v = 0
  · exact ⟨C0, Or.inl hv, c0_maximalFourAxioms, cone_specieslike 0⟩
  · exact ⟨C1, (c1_iff v).mpr (by omega), c1_maximalFourAxioms, cone_specieslike 1⟩

end SpeciesCones

#print axioms SpeciesCones.cone_fourAxioms
#print axioms SpeciesCones.cone_specieslike
#print axioms SpeciesCones.maximalFourAxioms_iff
#print axioms SpeciesCones.maximalFourAxioms_specieslike
#print axioms SpeciesCones.every_vertex_in_maximal_four_cluster
