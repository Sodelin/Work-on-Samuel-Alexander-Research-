import SamuelAlexanderResearch.ProductiveCore

namespace BoundaryRepair

open SpeciesBridge SpeciesGlobalIAP BinaryPopulation ProductiveCore

/-- Actual label deficiency after restricting the parent set. Original roots
also satisfy this predicate; they already have no incoming edges to delete. -/
def Deficient (E : LabelledGraph) (S : NatSet) : NatSet := fun v =>
  S v ∧ ∃ b, ¬ ∃ u, S u ∧ E u v b

def LostParent (E : LabelledGraph) (S : NatSet) : NatSet := fun v =>
  S v ∧ ∃ u, ¬ S u ∧ ForgetLabels E u v

def Repair (E : LabelledGraph) (S : NatSet) : LabelledGraph := fun u v b =>
  S u ∧ S v ∧ ¬ Deficient E S v ∧ E u v b

theorem repair_subgraph (E : LabelledGraph) (S : NatSet) (u v : Nat) (b : Bool)
    (h : Repair E S u v b) : E u v b := h.2.2.2

theorem not_deficient_parents {E : LabelledGraph} {S : NatSet} {v : Nat}
    (hv : S v) (h : ¬ Deficient E S v) : ∀ b, ∃ u, S u ∧ E u v b := by
  classical
  intro b
  exact Classical.byContradiction (fun hn => h ⟨hv, b, hn⟩)

theorem repair_root_iff {E : LabelledGraph} {S : NatSet} {v : Nat} (hv : S v) :
    Root (ProductiveCore.Induced (ForgetLabels (Repair E S)) S) v ↔ Deficient E S v := by
  classical
  constructor
  · intro hr
    apply Classical.byContradiction
    intro hn
    obtain ⟨u, hu, he⟩ := not_deficient_parents hv hn false
    exact hr u ⟨hu, hv, false, hu, hv, hn, he⟩
  · intro hd u hu
    obtain ⟨b, he⟩ := hu.2.2
    exact he.2.2.1 hd

theorem lostParent_finite {E : LabelledGraph} (p : BinaryNatPopulation E) (S : NatSet)
    (hremoved : FiniteSupport (fun v => ¬ S v)) : FiniteSupport (LostParent E S) := by
  obtain ⟨n, hn⟩ := (finiteSupport_iff_bounded _).mp hremoved
  obtain ⟨b, hb⟩ := PositiveUnavoidability.finite_union_bound (ForgetLabels E) n
    (fun u _ => (finiteSupport_iff_bounded _).mp (p.2.1.2.2.1 u))
  apply (finiteSupport_iff_bounded _).mpr
  refine ⟨b, ?_⟩
  rintro v ⟨_, u, hu, he⟩
  exact hb u (hn u hu) v he

theorem deficient_subset_roots_or_lostParent {E : LabelledGraph} (p : BinaryNatPopulation E)
    (S : NatSet) (v : Nat) (hv : Deficient E S v) :
    Root (ForgetLabels E) v ∨ LostParent E S v := by
  classical
  by_cases hr : Root (ForgetLabels E) v
  · exact Or.inl hr
  · obtain ⟨b, hb⟩ := hv.2
    obtain ⟨u, he⟩ := p.2.2.2 v hr b
    exact Or.inr ⟨hv.1, u, (fun hu => hb ⟨u, hu, he⟩), b, he⟩

theorem deficient_finite_of_cofinite {E : LabelledGraph} (p : BinaryNatPopulation E)
    (S : NatSet) (hremoved : FiniteSupport (fun v => ¬ S v)) : FiniteSupport (Deficient E S) :=
  finiteSupport_mono (deficient_subset_roots_or_lostParent p S)
    (finiteSupport_union p.2.2.1 (lostParent_finite p S hremoved))

theorem cofinite_infinite (S : NatSet) (hremoved : FiniteSupport (fun v => ¬ S v)) :
    InfiniteSupport S := by
  classical
  intro hS
  apply whole_infinite
  exact finiteSupport_mono (fun v _ => Classical.em (S v)) (finiteSupport_union hS hremoved)

/-- Finiteness of the actual deficient set is the exact extra boundary
hypothesis needed here. The retained set may have infinite complement. -/
theorem repair_population_of_finite_deficiency {E : LabelledGraph} (p : BinaryNatPopulation E)
    (S : NatSet) (hinfinite : InfiniteSupport S) (hdeficient : FiniteSupport (Deficient E S)) :
    PopulationOn (Repair E S) S := by
  refine ⟨?_, hinfinite, ?_, ?_, ?_, ?_⟩
  · intro u v a b ha hb
    exact p.1 u v a b ha.2.2.2 hb.2.2.2
  · intro u v _ _ he
    obtain ⟨b, hb⟩ := he
    exact p.2.1.1 u v ⟨b, hb.2.2.2⟩
  · intro u _
    apply finiteSupport_mono (T := ForgetLabels E u) _ (p.2.1.2.2.1 u)
    rintro v ⟨_, b, hb⟩
    exact ⟨b, hb.2.2.2⟩
  · exact finiteSupport_mono (fun _ h => (repair_root_iff h.1).mp h.2) hdeficient
  · intro v hv hn b
    have hnd : ¬ Deficient E S v := fun hd => hn ((repair_root_iff hv).mpr hd)
    obtain ⟨u, hu, he⟩ := not_deficient_parents hv hnd b
    exact ⟨u, hu, hu, hv, hnd, he⟩

theorem cofinite_repair_population {E : LabelledGraph} (p : BinaryNatPopulation E)
    (S : NatSet) (hremoved : FiniteSupport (fun v => ¬ S v)) : PopulationOn (Repair E S) S :=
  repair_population_of_finite_deficiency p S (cofinite_infinite S hremoved)
    (deficient_finite_of_cofinite p S hremoved)

theorem repair_preserves_child_cap (E : LabelledGraph) (S : NatSet) (d : Nat)
    (hcap : FixedGenderLift.ChildCap (ForgetLabels E) Whole d) :
    FixedGenderLift.ChildCap (ForgetLabels (Repair E S)) S d := by
  intro u _
  obtain ⟨xs, hlen, hxs⟩ := hcap u trivial
  refine ⟨xs, hlen, ?_⟩
  rintro v _ ⟨b, he⟩
  exact hxs v trivial ⟨b, he.2.2.2⟩

theorem repair_preserves_paths (E : LabelledGraph) (S : NatSet) (s : Nat → Bool) :
    Realizes (Repair E S) s → Realizes E s := by
  rintro ⟨path, hp⟩
  exact ⟨path, fun k => (hp k).2.2.2⟩

theorem repair_preserves_avoidance (E : LabelledGraph) (S : NatSet) (s : Nat → Bool)
    (h : ¬ Realizes E s) : ¬ Realizes (Repair E S) s :=
  fun hp => h (repair_preserves_paths E S s hp)

/-- A permissible deletion-only repair retains these same vertices, keeps
only original edges, and meets the original incoming-label rule at nonroots. -/
def AdmissibleRepair (E : LabelledGraph) (S : NatSet) (F : LabelledGraph) : Prop :=
  (∀ u v b, F u v b → Restrict E S u v b) ∧
  (∀ v, S v → ¬ Root (ProductiveCore.Induced (ForgetLabels F) S) v →
    ∀ b, ∃ u, S u ∧ F u v b)

theorem repair_admissible (E : LabelledGraph) (S : NatSet) : AdmissibleRepair E S (Repair E S) := by
  constructor
  · intro u v b h
    exact ⟨h.1, h.2.1, h.2.2.2⟩
  · intro v hv hn b
    have hnd := fun hd => hn ((repair_root_iff hv).mpr hd)
    obtain ⟨u, hu, he⟩ := not_deficient_parents hv hnd b
    exact ⟨u, hu, hu, hv, hnd, he⟩

theorem deficient_forced_root (E : LabelledGraph) (S : NatSet) (F : LabelledGraph)
    (hF : AdmissibleRepair E S F) (v : Nat) (hv : Deficient E S v) :
    Root (ProductiveCore.Induced (ForgetLabels F) S) v := by
  classical
  intro u hu
  have hn : ¬ Root (ProductiveCore.Induced (ForgetLabels F) S) v := fun hr => hr u hu
  obtain ⟨b, hb⟩ := hv.2
  obtain ⟨a, ha, he⟩ := hF.2 v hv.1 hn b
  exact hb ⟨a, ha, (hF.1 a v b he).2.2⟩

/-- The canonical repair is the greatest permissible edge subrelation.
Equivalently, its deleted edge set and root set are inclusion-minimal. -/
theorem repair_greatest (E : LabelledGraph) (S : NatSet) (F : LabelledGraph)
    (hF : AdmissibleRepair E S F) : ∀ u v b, F u v b → Repair E S u v b := by
  intro u v b he
  have h := hF.1 u v b he
  refine ⟨h.1, h.2.1, ?_, h.2.2⟩
  intro hd
  exact deficient_forced_root E S F hF v hd u ⟨h.1, h.2.1, b, he⟩

theorem repair_minimal_roots (E : LabelledGraph) (S : NatSet) (F : LabelledGraph)
    (hF : AdmissibleRepair E S F) (v : Nat) (hv : S v)
    (hr : Root (ProductiveCore.Induced (ForgetLabels (Repair E S)) S) v) :
    Root (ProductiveCore.Induced (ForgetLabels F) S) v :=
  deficient_forced_root E S F hF v ((repair_root_iff hv).mp hr)

/-- An exact existence criterion for an eligible deletion-only repair on a
fixed infinite retained set. No cofinite-complement hypothesis is necessary. -/
theorem finite_deficiency_iff_repair_exists {E : LabelledGraph} (p : BinaryNatPopulation E)
    (S : NatSet) (hinfinite : InfiniteSupport S) :
    FiniteSupport (Deficient E S) ↔
      ∃ F, AdmissibleRepair E S F ∧ PopulationOn F S := by
  constructor
  · intro hf
    exact ⟨Repair E S, repair_admissible E S,
      repair_population_of_finite_deficiency p S hinfinite hf⟩
  · rintro ⟨F, hF, hp⟩
    exact finiteSupport_mono
      (fun v hv => ⟨hv.1, deficient_forced_root E S F hF v hv⟩) hp.roots

theorem repair_deleted_edges_bounded {E : LabelledGraph} (p : BinaryNatPopulation E)
    (S : NatSet) (hdeficient : FiniteSupport (Deficient E S)) :
    ∃ bound, ∀ u v b, Restrict E S u v b → ¬ Repair E S u v b →
      u < bound ∧ v < bound := by
  classical
  obtain ⟨bound, hb⟩ := (finiteSupport_iff_bounded _).mp hdeficient
  refine ⟨bound, ?_⟩
  intro u v b he hn
  have hd : Deficient E S v :=
    Classical.byContradiction (fun hnd => hn ⟨he.1, he.2.1, hnd, he.2.2⟩)
  have hv := hb v hd
  have hu := p.2.1.1 u v ⟨b, he.2.2⟩
  exact ⟨Nat.lt_trans hu hv, hv⟩

theorem finite_boundary_repair_theorem {E : LabelledGraph} (p : BinaryNatPopulation E)
    (S : NatSet) (hinfinite : InfiniteSupport S) (hdeficient : FiniteSupport (Deficient E S))
    (d : Nat) (hcap : FixedGenderLift.ChildCap (ForgetLabels E) Whole d) :
    let q := repair_population_of_finite_deficiency p S hinfinite hdeficient
    BinaryNatPopulation (reindexed q) ∧
    FixedGenderLift.ChildCap (ForgetLabels (reindexed q)) Whole d ∧
    (∀ s, ¬ Realizes E s → ¬ Realizes (reindexed q) s) ∧
    (∀ i, Root (ForgetLabels (reindexed q)) i ↔ Deficient E S (vertex q i)) := by
  dsimp only
  let q := repair_population_of_finite_deficiency p S hinfinite hdeficient
  refine ⟨reindexed_population q, reindexed_child_cap q d (repair_preserves_child_cap E S d hcap),
    ?_, ?_⟩
  · intro s hs hp
    have hr := (reindexed_realizes_iff q s).mp hp
    exact repair_preserves_avoidance E S s hs
      (restriction_preserves_paths (Repair E S) S s hr)
  · intro i
    exact (reindexed_root_iff q i).trans (repair_root_iff (vertex_mem q i))

theorem ps_nonroot_deficient_iff (s : Nat → Bool) (S : NatSet) (v : Nat) (hv : 2 ≤ v) :
    Deficient (BinaryAvoidance.Edge s) S v ↔ S v ∧ (¬ S (v - 1) ∨ ¬ S (v - 2)) := by
  classical
  constructor
  · rintro ⟨hS, b, hb⟩
    refine ⟨hS, ?_⟩
    by_cases h1 : S (v - 1)
    · apply Or.inr
      intro h2
      obtain ⟨u, hu⟩ := incoming_each_label s v hv b
      rcases (incoming_parents_iff s v hv u).mp ⟨b, hu⟩ with h | h
      · exact hb ⟨u, h ▸ h1, hu⟩
      · exact hb ⟨u, h ▸ h2, hu⟩
    · exact Or.inl h1
  · rintro ⟨hS, h1 | h2⟩
    · refine ⟨hS, BinaryAvoidance.row s v, ?_⟩
      rintro ⟨u, hu, he⟩
      have heq := incoming_parent_unique s v (BinaryAvoidance.row s v)
        he (two_distinct_parents s v hv).1
      exact h1 (heq ▸ hu)
    · refine ⟨hS, !(BinaryAvoidance.row s v), ?_⟩
      rintro ⟨u, hu, he⟩
      have heq := incoming_parent_unique s v (!(BinaryAvoidance.row s v))
        he (two_distinct_parents s v hv).2.1
      exact h2 (heq ▸ hu)

theorem ps_deficient_iff (s : Nat → Bool) (S : NatSet) (v : Nat) :
    Deficient (BinaryAvoidance.Edge s) S v ↔
      S v ∧ (v < 2 ∨ ¬ S (v - 1) ∨ ¬ S (v - 2)) := by
  by_cases hv : 2 ≤ v
  · rw [ps_nonroot_deficient_iff s S v hv]
    simp only [show ¬ v < 2 by omega, false_or]
  · constructor
    · intro h
      exact ⟨h.1, Or.inl (by omega)⟩
    · intro h
      refine ⟨h.1, false, ?_⟩
      rintro ⟨u, _, he⟩
      exact hv he.1

theorem ps_c0_deficient_iff (s : Nat → Bool) (v : Nat) :
    Deficient (BinaryAvoidance.Edge s) SpeciesCones.C0 v ↔ v = 0 ∨ v = 2 ∨ v = 3 := by
  rw [ps_deficient_iff]
  simp only [SpeciesCones.c0_iff]
  omega

theorem ps_c1_deficient_iff (s : Nat → Bool) (v : Nat) :
    Deficient (BinaryAvoidance.Edge s) SpeciesCones.C1 v ↔ v = 1 ∨ v = 2 := by
  rw [ps_deficient_iff]
  simp only [SpeciesCones.c1_iff]
  omega

theorem ps_c0_repair_roots (s : Nat → Bool) (v : Nat) :
    (SpeciesCones.C0 v ∧ Root (ProductiveCore.Induced
      (ForgetLabels (Repair (BinaryAvoidance.Edge s) SpeciesCones.C0)) SpeciesCones.C0) v) ↔
      v = 0 ∨ v = 2 ∨ v = 3 := by
  constructor
  · intro h
    exact (ps_c0_deficient_iff s v).mp ((repair_root_iff h.1).mp h.2)
  · intro h
    have hd := (ps_c0_deficient_iff s v).mpr h
    exact ⟨hd.1, (repair_root_iff hd.1).mpr hd⟩

theorem ps_c1_repair_roots (s : Nat → Bool) (v : Nat) :
    (SpeciesCones.C1 v ∧ Root (ProductiveCore.Induced
      (ForgetLabels (Repair (BinaryAvoidance.Edge s) SpeciesCones.C1)) SpeciesCones.C1) v) ↔
      v = 1 ∨ v = 2 := by
  constructor
  · intro h
    exact (ps_c1_deficient_iff s v).mp ((repair_root_iff h.1).mp h.2)
  · intro h
    have hd := (ps_c1_deficient_iff s v).mpr h
    exact ⟨hd.1, (repair_root_iff hd.1).mpr hd⟩

theorem ps_c0_cut_edges (s : Nat → Bool) (u v : Nat) (b : Bool) :
    (Restrict (BinaryAvoidance.Edge s) SpeciesCones.C0 u v b ∧
      ¬ Repair (BinaryAvoidance.Edge s) SpeciesCones.C0 u v b) ↔
    ((u = 0 ∧ v = 2) ∨ (u = 2 ∧ v = 3)) ∧ BinaryAvoidance.Edge s u v b := by
  classical
  constructor
  · rintro ⟨he, hn⟩
    have hd : Deficient (BinaryAvoidance.Edge s) SpeciesCones.C0 v :=
      Classical.byContradiction (fun hnd => hn ⟨he.1, he.2.1, hnd, he.2.2⟩)
    have hv := (ps_c0_deficient_iff s v).mp hd
    have hu := (SpeciesCones.c0_iff u).mp he.1
    have hg := (forget_edge_iff s u v).mp ⟨b, he.2.2⟩
    refine ⟨?_, he.2.2⟩
    unfold PsEdge at hg
    omega
  · rintro ⟨h, he⟩
    have hu : SpeciesCones.C0 u := (SpeciesCones.c0_iff u).mpr (by omega)
    have hv : SpeciesCones.C0 v := (SpeciesCones.c0_iff v).mpr (by omega)
    have hd := (ps_c0_deficient_iff s v).mpr (by omega)
    exact ⟨⟨hu, hv, he⟩, fun hr => hr.2.2.1 hd⟩

theorem ps_c1_cut_edges (s : Nat → Bool) (u v : Nat) (b : Bool) :
    (Restrict (BinaryAvoidance.Edge s) SpeciesCones.C1 u v b ∧
      ¬ Repair (BinaryAvoidance.Edge s) SpeciesCones.C1 u v b) ↔
    (u = 1 ∧ v = 2) ∧ BinaryAvoidance.Edge s u v b := by
  classical
  constructor
  · rintro ⟨he, hn⟩
    have hd : Deficient (BinaryAvoidance.Edge s) SpeciesCones.C1 v :=
      Classical.byContradiction (fun hnd => hn ⟨he.1, he.2.1, hnd, he.2.2⟩)
    have hv := (ps_c1_deficient_iff s v).mp hd
    have hu := (SpeciesCones.c1_iff u).mp he.1
    have hg := (forget_edge_iff s u v).mp ⟨b, he.2.2⟩
    refine ⟨?_, he.2.2⟩
    unfold PsEdge at hg
    omega
  · rintro ⟨h, he⟩
    have hu : SpeciesCones.C1 u := (SpeciesCones.c1_iff u).mpr (by omega)
    have hv : SpeciesCones.C1 v := (SpeciesCones.c1_iff v).mpr (by omega)
    have hd := (ps_c1_deficient_iff s v).mpr (by omega)
    exact ⟨⟨hu, hv, he⟩, fun hr => hr.2.2.1 hd⟩

theorem ps_c0_repair_zero_isolated (s : Nat → Bool) (v : Nat) :
    ¬ ForgetLabels (Repair (BinaryAvoidance.Edge s) SpeciesCones.C0) 0 v ∧
    ¬ ForgetLabels (Repair (BinaryAvoidance.Edge s) SpeciesCones.C0) v 0 := by
  constructor
  · rintro ⟨b, h⟩
    have hv := (SpeciesCones.c0_iff v).mp h.2.1
    have he := (forget_edge_iff s 0 v).mp ⟨b, h.2.2.2⟩
    have hd := (ps_c0_deficient_iff s v).mpr (by unfold PsEdge at he; omega)
    exact h.2.2.1 hd
  · rintro ⟨b, h⟩
    have := h.2.2.2.1
    omega

theorem ps_c0_repair_not_connected (s : Nat → Bool) :
    ¬ WeaklyConnected (ForgetLabels (Repair (BinaryAvoidance.Edge s) SpeciesCones.C0))
      SpeciesCones.C0 := by
  intro hconn
  have h := hconn.2 0 2 ((SpeciesCones.c0_iff _).mpr (by omega))
    ((SpeciesCones.c0_iff _).mpr (by omega))
  have stays : ∀ {u v}, WeakReach
      (ForgetLabels (Repair (BinaryAvoidance.Edge s) SpeciesCones.C0)) SpeciesCones.C0 u v →
      u = 0 → v = 0 := by
    intro u v hr
    induction hr with
    | refl _ => exact id
    | edge _ _ he =>
      intro hu
      subst hu
      rcases he with he | he
      · exact False.elim ((ps_c0_repair_zero_isolated s _).1 he)
      · exact False.elim ((ps_c0_repair_zero_isolated s _).2 he)
    | trans _ _ ih1 ih2 => exact fun hu => ih2 (ih1 hu)
  have := stays h rfl
  omega

theorem ps_c1_repair_shifted_geometry (s : Nat → Bool) (u v : Nat) :
    ForgetLabels (Repair (BinaryAvoidance.Edge s) SpeciesCones.C1) (u + 1) (v + 1) ↔
      PsEdge u v := by
  constructor
  · rintro ⟨b, h⟩
    have he := (forget_edge_iff s (u + 1) (v + 1)).mp ⟨b, h.2.2.2⟩
    have hd : ¬ (v + 1 = 1 ∨ v + 1 = 2) :=
      fun hd => h.2.2.1 ((ps_c1_deficient_iff s (v + 1)).mpr hd)
    unfold PsEdge at he ⊢
    omega
  · intro h
    obtain ⟨b, he⟩ := (forget_edge_iff s (u + 1) (v + 1)).mpr (by unfold PsEdge at h ⊢; omega)
    refine ⟨b, (SpeciesCones.c1_iff _).mpr (by omega), (SpeciesCones.c1_iff _).mpr (by omega), ?_, he⟩
    intro hd
    have := (ps_c1_deficient_iff s (v + 1)).mp hd
    have := h.1
    omega

end BoundaryRepair

#print axioms BoundaryRepair.deficient_finite_of_cofinite
#print axioms BoundaryRepair.cofinite_repair_population
#print axioms BoundaryRepair.finite_deficiency_iff_repair_exists
#print axioms BoundaryRepair.repair_greatest
#print axioms BoundaryRepair.repair_minimal_roots
#print axioms BoundaryRepair.repair_deleted_edges_bounded
#print axioms BoundaryRepair.finite_boundary_repair_theorem
#print axioms BoundaryRepair.ps_c0_repair_roots
#print axioms BoundaryRepair.ps_c1_repair_roots
#print axioms BoundaryRepair.ps_c0_cut_edges
#print axioms BoundaryRepair.ps_c1_cut_edges
#print axioms BoundaryRepair.ps_c0_repair_not_connected
#print axioms BoundaryRepair.ps_c1_repair_shifted_geometry
