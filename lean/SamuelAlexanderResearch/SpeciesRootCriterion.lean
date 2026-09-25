import SamuelAlexanderResearch.SpeciesCones

/-!
# The root-cone criterion for maximal four-property sets

All species predicates are those of `SpeciesBridge`, in the fixed ambient
graph. The parameterized cone and maximality definitions below specialize
definitionally to `SpeciesCones`; explicit bridges record this fact.

Root coverage suffices for the general characterization. Strict chronological
edges on `Nat` imply that coverage, with no finite-root or finite-child premise.
This is a direct deduction from the cited species definitions, not a priority
claim about the root-clade pattern.
-/

namespace SpeciesRootCriterion

open SpeciesBridge

def Cone (E : Graph) (root : Nat) : NatSet :=
  fun v => v = root ∨ Descendant E root v

def FourAxioms (E : Graph) (S : NatSet) : Prop :=
  IAP E S ∧ Convex E S ∧ CommonAncestor E S ∧ Reflection E S

def MaximalFourAxioms (E : Graph) (S : NatSet) : Prop :=
  FourAxioms E S ∧ ∀ T : NatSet,
    (∀ v, S v → T v) → FourAxioms E T → ∀ v, T v → S v

theorem cone_ps_eq (root : Nat) : Cone PsEdge root = SpeciesCones.Cone root := rfl

theorem fourAxioms_ps_iff (S : NatSet) :
    FourAxioms PsEdge S ↔ SpeciesCones.FourAxioms S := Iff.rfl

theorem maximalFourAxioms_ps_iff (S : NatSet) :
    MaximalFourAxioms PsEdge S ↔ SpeciesCones.MaximalFourAxioms S := Iff.rfl

theorem cone_closed_under_descendants (E : Graph) (root v w : Nat)
    (hv : Cone E root v) (hvw : Descendant E v w) : Cone E root w := by
  apply Or.inr
  rcases hv with h | h
  · subst v
    exact hvw
  · exact h.trans hvw

theorem cone_commonAncestor (E : Graph) (root : Nat) :
    CommonAncestor E (Cone E root) := by
  refine ⟨root, Or.inl rfl, ?_⟩
  intro w hw hne
  rcases hw with h | h
  · exact False.elim (hne h)
  · exact h

theorem cone_convex (E : Graph) (root : Nat) : Convex E (Cone E root) := by
  intro v hancestor _
  obtain ⟨a, ha, hav⟩ := hancestor
  exact cone_closed_under_descendants E root a v ha hav

theorem cone_reflection (E : Graph) (root : Nat) : Reflection E (Cone E root) := by
  intro v hv hinfinite hfinite
  apply hinfinite
  apply finiteSupport_mono _ hfinite
  intro w hw
  exact ⟨cone_closed_under_descendants E root v w hv hw, hw⟩

private theorem descendant_weakReach_in_cone {E : Graph} {root v : Nat}
    (h : Descendant E root v) : WeakReach E (Cone E root) root v := by
  induction h with
  | edge h =>
    exact .edge (Or.inl rfl) (Or.inr (.edge h)) (Or.inl h)
  | snoc h hlast ih =>
    exact .trans ih (.edge (Or.inr h) (Or.inr (.snoc h hlast)) (Or.inl hlast))

theorem cone_weaklyConnected (E : Graph) (root : Nat) :
    WeaklyConnected E (Cone E root) := by
  refine ⟨⟨root, Or.inl rfl⟩, ?_⟩
  have fromRoot : ∀ v, Cone E root v → WeakReach E (Cone E root) root v := by
    intro v hv
    rcases hv with h | h
    · subst v
      exact .refl (Or.inl rfl)
    · exact descendant_weakReach_in_cone h
  intro u v hu hv
  exact .trans (fromRoot u hu).symm (fromRoot v hv)

theorem cone_fourAxioms (E : Graph) (root : Nat) (hIAP : IAP E (Cone E root)) :
    FourAxioms E (Cone E root) :=
  ⟨hIAP, cone_convex E root, cone_commonAncestor E root, cone_reflection E root⟩

theorem cone_specieslike (E : Graph) (root : Nat) (hIAP : IAP E (Cone E root)) :
    Specieslike E (Cone E root) :=
  ⟨cone_weaklyConnected E root, hIAP, cone_convex E root⟩

theorem root_has_no_ancestor {E : Graph} {root u : Nat}
    (hroot : Root E root) : ¬ Descendant E u root := by
  intro h
  cases h with
  | edge h => exact hroot _ h
  | snoc _ h => exact hroot _ h

/-- Every vertex belongs to the cone of a vertex with no incoming edges. -/
def RootCovered (E : Graph) : Prop :=
  ∀ v, ∃ root, Root E root ∧ Cone E root v

/-- Natural birth order supplies root coverage by induction on the vertex. -/
theorem rootCovered_of_strict_birth_order (E : Graph)
    (horder : ∀ u v, E u v → u < v) : RootCovered E := by
  classical
  intro v
  induction v using Nat.strongRecOn with
  | ind v ih =>
    by_cases hroot : Root E v
    · exact ⟨v, hroot, Or.inl rfl⟩
    · have hparent : ∃ u, E u v := by
        apply Classical.byContradiction
        intro hn
        apply hroot
        intro u hu
        exact hn ⟨u, hu⟩
      obtain ⟨u, huv⟩ := hparent
      obtain ⟨root, hr, hru⟩ := ih u (horder u v huv)
      exact ⟨root, hr, cone_closed_under_descendants E root u v hru (.edge huv)⟩

theorem commonAncestor_subset_root_cone (E : Graph) (hcovered : RootCovered E)
    (S : NatSet) (hCA : CommonAncestor E S) :
    ∃ root, Root E root ∧ ∀ v, S v → Cone E root v := by
  classical
  obtain ⟨a, _, ha⟩ := hCA
  obtain ⟨root, hr, hra⟩ := hcovered a
  refine ⟨root, hr, ?_⟩
  intro v hv
  by_cases heq : v = a
  · subst v
    exact hra
  · exact cone_closed_under_descendants E root a v hra (ha v hv heq)

/-- A common-ancestor set containing a root is confined to that root's cone. -/
theorem commonAncestor_subset_cone_of_root_mem (E : Graph) (S : NatSet)
    (root : Nat) (hroot : Root E root) (hmem : S root)
    (hCA : CommonAncestor E S) : ∀ v, S v → Cone E root v := by
  classical
  obtain ⟨a, _, ha⟩ := hCA
  have heq : root = a := by
    by_cases heq : root = a
    · exact heq
    · exact False.elim (root_has_no_ancestor hroot (ha root hmem heq))
  subst a
  intro v hv
  by_cases heq : v = root
  · exact Or.inl heq
  · exact Or.inr (ha v hv heq)

theorem root_cone_subset_iff_root_eq (E : Graph) (root other : Nat)
    (hroot : Root E root) :
    (∀ v, Cone E root v → Cone E other v) ↔ root = other := by
  constructor
  · intro h
    rcases h root (Or.inl rfl) with heq | hdesc
    · exact heq
    · exact False.elim (root_has_no_ancestor hroot hdesc)
  · intro heq
    subst other
    exact fun _ h => h

theorem root_cone_maximal (E : Graph) (root : Nat) (hroot : Root E root)
    (hIAP : IAP E (Cone E root)) : MaximalFourAxioms E (Cone E root) := by
  refine ⟨cone_fourAxioms E root hIAP, ?_⟩
  intro T hsub hT
  exact commonAncestor_subset_cone_of_root_mem E T root hroot
    (hsub root (Or.inl rfl)) hT.2.2.1

def RootConesIAP (E : Graph) : Prop :=
  ∀ root, Root E root → IAP E (Cone E root)

def RootConeClassification (E : Graph) : Prop :=
  ∀ S : NatSet, MaximalFourAxioms E S ↔ ∃ root, Root E root ∧ S = Cone E root

theorem maximalFourAxioms_iff_root_cone (E : Graph) (hcovered : RootCovered E)
    (hIAP : RootConesIAP E) (S : NatSet) :
    MaximalFourAxioms E S ↔ ∃ root, Root E root ∧ S = Cone E root := by
  constructor
  · intro hS
    obtain ⟨root, hr, hsub⟩ := commonAncestor_subset_root_cone E hcovered S hS.1.2.2.1
    have hrev := hS.2 (Cone E root) hsub (cone_fourAxioms E root (hIAP root hr))
    refine ⟨root, hr, ?_⟩
    funext v
    exact propext ⟨hsub v, hrev v⟩
  · rintro ⟨root, hr, rfl⟩
    exact root_cone_maximal E root hr (hIAP root hr)

/-- Exact criterion: the maximal four-property family is precisely the family
of all root cones if and only if every root cone has IAP. -/
theorem root_cone_criterion (E : Graph) (hcovered : RootCovered E) :
    RootConesIAP E ↔ RootConeClassification E := by
  constructor
  · intro hIAP S
    exact maximalFourAxioms_iff_root_cone E hcovered hIAP S
  · intro hclass root hr
    have hmax := (hclass (Cone E root)).mpr ⟨root, hr, rfl⟩
    exact hmax.1.1

theorem root_cone_criterion_of_strict_birth_order (E : Graph)
    (horder : ∀ u v, E u v → u < v) :
    RootConesIAP E ↔ RootConeClassification E :=
  root_cone_criterion E (rootCovered_of_strict_birth_order E horder)

theorem maximalFourAxioms_specieslike (E : Graph) (hcovered : RootCovered E)
    (hIAP : RootConesIAP E) (S : NatSet) (hS : MaximalFourAxioms E S) :
    Specieslike E S := by
  obtain ⟨root, hr, rfl⟩ := (maximalFourAxioms_iff_root_cone E hcovered hIAP S).mp hS
  exact cone_specieslike E root (hIAP root hr)

theorem every_vertex_in_maximal_four_cluster (E : Graph) (hcovered : RootCovered E)
    (hIAP : RootConesIAP E) (v : Nat) :
    ∃ S : NatSet, S v ∧ MaximalFourAxioms E S ∧ Specieslike E S := by
  obtain ⟨root, hr, hrv⟩ := hcovered v
  exact ⟨Cone E root, hrv, root_cone_maximal E root hr (hIAP root hr),
    cone_specieslike E root (hIAP root hr)⟩

end SpeciesRootCriterion

#print axioms SpeciesRootCriterion.cone_ps_eq
#print axioms SpeciesRootCriterion.maximalFourAxioms_ps_iff
#print axioms SpeciesRootCriterion.cone_weaklyConnected
#print axioms SpeciesRootCriterion.rootCovered_of_strict_birth_order
#print axioms SpeciesRootCriterion.root_cone_maximal
#print axioms SpeciesRootCriterion.maximalFourAxioms_iff_root_cone
#print axioms SpeciesRootCriterion.root_cone_criterion
#print axioms SpeciesRootCriterion.root_cone_criterion_of_strict_birth_order
#print axioms SpeciesRootCriterion.maximalFourAxioms_specieslike
#print axioms SpeciesRootCriterion.every_vertex_in_maximal_four_cluster
