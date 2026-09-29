import SamuelAlexanderResearch.SpeciesBridge

/-!
An extinction-permitting generation model. Synchronizing blocks are defined
using actual parenthood paths, not an assumed lineage-fate predicate.
This is a formal bridge for Alexander (2026), Section 3.1's first informal
argument, with a converse in this discrete finite-generation setting.
-/
namespace ExtinctionPedigree
open SpeciesBridge

structure Model where
  edge : Graph
  generation : Nat → Nat
  finitePast : ∀ n, FiniteSupport (fun v => generation v < n)
  occupied : ∀ n, ∃ v, generation v = n
  edgeStep : ∀ u v, edge u v → generation v = generation u + 1
  parent : ∀ v, 0 < generation v → ∃ u, edge u v

namespace Model
variable (G : Model)

def Sync (t T : Nat) : Prop :=
  t < T ∧ ∀ u v w, G.generation u = t →
    G.generation v = T → G.generation w = T →
    (Descendant G.edge u v ↔ Descendant G.edge u w)

def LateSync : Prop := ∀ N, ∃ t T, N ≤ t ∧ G.Sync t T

def AllFrom (u T : Nat) : Prop :=
  ∀ v, T ≤ G.generation v → Descendant G.edge u v

def NoneFrom (u T : Nat) : Prop :=
  ∀ v, T ≤ G.generation v → ¬ Descendant G.edge u v

def ResolvedFrom (u T : Nat) : Prop := G.NoneFrom u T ∨ G.AllFrom u T

theorem descendant_generation_lt {u v : Nat} (h : Descendant G.edge u v) :
    G.generation u < G.generation v := by
  induction h with
  | edge he => have := G.edgeStep _ _ he; omega
  | snoc _ he ih => have := G.edgeStep _ _ he; omega

theorem adjacent_descendant_iff_edge {u v : Nat}
    (hgen : G.generation v = G.generation u + 1) :
    Descendant G.edge u v ↔ G.edge u v := by
  constructor
  · intro h
    cases h with
    | edge he => exact he
    | @snoc x y hxy hyz =>
      have := G.descendant_generation_lt hxy
      have := G.edgeStep _ _ hyz
      omega
  · exact Descendant.edge

theorem descendant_cut {u v : Nat} (h : Descendant G.edge u v)
    {t : Nat} (hu : G.generation u < t) (hv : t < G.generation v) :
    ∃ x, G.generation x = t ∧ Descendant G.edge u x ∧ Descendant G.edge x v := by
  induction h with
  | edge he => have := G.edgeStep _ _ he; omega
  | @snoc b c hab hbc ih =>
    have hstep := G.edgeStep _ _ hbc
    by_cases ht : t < G.generation b
    · obtain ⟨x,hx,hax,hxb⟩ := ih ht
      exact ⟨x,hx,hax,Descendant.snoc hxb hbc⟩
    · have hbt : G.generation b = t := by omega
      exact ⟨b,hbt,hab,Descendant.edge hbc⟩

theorem sync_resolves_cohort {t T u : Nat} (hs : G.Sync t T)
    (hu : G.generation u < t) :
    (∀ v, G.generation v = T → ¬ Descendant G.edge u v) ∨
    (∀ v, G.generation v = T → Descendant G.edge u v) := by
  classical
  have htT := hs.1
  obtain ⟨w,hw⟩ := G.occupied T
  by_cases huw : Descendant G.edge u w
  · right
    obtain ⟨x,hx,hux,hxw⟩ := G.descendant_cut huw hu (by omega)
    intro v hv
    exact hux.trans ((hs.2 x w v hx hw hv).mp hxw)
  · left
    intro v hv huv
    obtain ⟨x,hx,hux,hxv⟩ := G.descendant_cut huv hu (by omega)
    exact huw (hux.trans ((hs.2 x v w hx hv hw).mp hxv))

theorem all_cohort_persists {u T : Nat}
    (h : ∀ v, G.generation v = T → Descendant G.edge u v) :
    G.AllFrom u T := by
  have hcohort : ∀ n, ∀ v, G.generation v = T+n → Descendant G.edge u v := by
    intro n
    induction n with
    | zero => simpa using h
    | succ n ih =>
      intro v hv
      obtain ⟨w,hw⟩ := G.parent v (by omega)
      have hg := G.edgeStep _ _ hw
      exact Descendant.snoc (ih w (by omega)) hw
  intro v hv
  exact hcohort (G.generation v-T) v (by omega)

theorem none_cohort_persists {u T : Nat} (hu : G.generation u < T)
    (h : ∀ v, G.generation v = T → ¬ Descendant G.edge u v) :
    G.NoneFrom u T := by
  have hcohort : ∀ n, ∀ v, G.generation v = T+n → ¬ Descendant G.edge u v := by
    intro n
    induction n with
    | zero => simpa using h
    | succ n ih =>
      intro v hv hd
      cases hd with
      | edge he => have := G.edgeStep _ _ he; omega
      | @snoc b c hab hbc =>
        have hg := G.edgeStep _ _ hbc
        exact ih b (by omega) hab
  intro v hv
  exact hcohort (G.generation v-T) v (by omega)

theorem late_sync_resolves (h : G.LateSync) (u : Nat) :
    ∃ T, G.ResolvedFrom u T := by
  obtain ⟨t,T,ht,hs⟩ := h (G.generation u+1)
  refine ⟨T,?_⟩
  rcases G.sync_resolves_cohort (u := u) hs (by omega) with hnone | hall
  · exact Or.inl (G.none_cohort_persists (by have := hs.1; omega) hnone)
  · exact Or.inr (G.all_cohort_persists hall)

theorem resolved_finite_or_cofinite {u T : Nat} (h : G.ResolvedFrom u T) :
    FiniteSupport (Descendant G.edge u) ∨
    FiniteSupport (fun v => ¬ Descendant G.edge u v) := by
  rcases h with hn | ha
  · left
    apply finiteSupport_mono (T := fun v => G.generation v < T) ?_ (G.finitePast T)
    intro v hv
    apply Classical.byContradiction
    intro ht
    exact hn v (by omega) hv
  · right
    apply finiteSupport_mono (T := fun v => G.generation v < T) ?_ (G.finitePast T)
    intro v hv
    apply Classical.byContradiction
    intro ht
    exact hv (ha v (by omega))

theorem late_sync_every_subset_iap (h : G.LateSync) (S : NatSet) :
    IAP G.edge S := by
  intro u _
  obtain ⟨T,hT⟩ := G.late_sync_resolves h u
  rcases G.resolved_finite_or_cofinite hT with hn | ha
  · exact Or.inl (finiteSupport_mono (fun _ hv => hv.2) hn)
  · exact Or.inr (finiteSupport_mono (fun _ hv => hv.2) ha)

private theorem member_le_sum {xs : List Nat} {n : Nat} (h : n ∈ xs) :
    n ≤ xs.sum := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.mem_cons] at h
    simp only [List.sum_cons]
    rcases h with rfl | h
    · omega
    · have := ih h; omega

theorem finite_generation_bound {S : NatSet} (hS : FiniteSupport S) :
    ∃ N, ∀ v, S v → G.generation v < N := by
  obtain ⟨xs,hxs⟩ := hS
  refine ⟨(xs.map G.generation).sum+1,?_⟩
  intro v hv
  have hm : G.generation v ∈ xs.map G.generation :=
    List.mem_map.mpr ⟨v,hxs v hv,rfl⟩
  have := member_le_sum hm
  omega

theorem global_iap_resolves (h : IAP G.edge Whole) (u : Nat) :
    ∃ T, G.ResolvedFrom u T := by
  rcases h u trivial with hn | ha
  · obtain ⟨T,hT⟩ := G.finite_generation_bound hn
    exact ⟨T,Or.inl (by
      intro v hv hd
      have := hT v ⟨trivial,hd⟩
      omega)⟩
  · obtain ⟨T,hT⟩ := G.finite_generation_bound ha
    refine ⟨T,Or.inr ?_⟩
    intro v hv
    classical
    apply Classical.byContradiction
    intro hd
    have := hT v ⟨trivial,hd⟩
    omega

theorem global_iap_sync_after (h : IAP G.edge Whole) (t : Nat) :
    ∃ T, G.Sync t T := by
  classical
  obtain ⟨xs,hxs⟩ := G.finitePast (t+1)
  let f : Nat → Nat := fun u => Classical.choose (G.global_iap_resolves h u)
  have hf : ∀ u, G.ResolvedFrom u (f u) :=
    fun u => Classical.choose_spec (G.global_iap_resolves h u)
  let T := max (t+1) (xs.map f).sum
  refine ⟨T,by dsimp [T]; omega,?_⟩
  intro u v w hu hv hw
  have hm : u ∈ xs := hxs u (by omega)
  have hm' : f u ∈ xs.map f := List.mem_map.mpr ⟨u,hm,rfl⟩
  have hle := member_le_sum hm'
  have hfv : f u ≤ G.generation v := by dsimp [T] at hv; omega
  have hfw : f u ≤ G.generation w := by dsimp [T] at hw; omega
  rcases hf u with hn | ha
  · exact ⟨fun hd => False.elim (hn v hfv hd),
      fun hd => False.elim (hn w hfw hd)⟩
  · exact ⟨fun _ => ha w hfw,fun _ => ha v hfv⟩

theorem global_iap_iff_late_sync :
    IAP G.edge Whole ↔ G.LateSync := by
  constructor
  · intro h N
    obtain ⟨T,hT⟩ := G.global_iap_sync_after h N
    exact ⟨N,T,Nat.le_refl N,hT⟩
  · intro h
    exact G.late_sync_every_subset_iap h Whole

theorem common_parents_sync (t : Nat)
    (h : ∀ u v w, G.generation u = t →
      G.generation v = t+1 → G.generation w = t+1 →
      (G.edge u v ↔ G.edge u w)) : G.Sync t (t+1) := by
  refine ⟨by omega,?_⟩
  intro u v w hu hv hw
  rw [G.adjacent_descendant_iff_edge (by omega),
    G.adjacent_descendant_iff_edge (by omega)]
  exact h u v w hu hv hw

end Model

/-- Three organisms per generation; indices 0 and 1 are the shared pair of
parents for every child. Index 2 in every generation is childless. -/
def pairModel : Model where
  edge u v := v/3 = u/3+1 ∧ u%3 < 2
  generation v := v/3
  finitePast n := (finiteSupport_iff_bounded _).mpr ⟨3*n,by
    intro v hv
    omega⟩
  occupied n := ⟨3*n,by omega⟩
  edgeStep _ _ h := h.1
  parent v hv := ⟨3*(v/3-1),by constructor <;> omega⟩

theorem pairModel_late_sync : pairModel.LateSync := by
  intro N
  refine ⟨N,N+1,Nat.le_refl N,pairModel.common_parents_sync N ?_⟩
  intro u v w hu hv hw
  change u/3 = N at hu
  change v/3 = N+1 at hv
  change w/3 = N+1 at hw
  change (v/3 = u/3+1 ∧ u%3 < 2) ↔ (w/3 = u/3+1 ∧ u%3 < 2)
  simp [hu,hv,hw]

theorem pairModel_iap : IAP pairModel.edge Whole :=
  pairModel.late_sync_every_subset_iap pairModel_late_sync Whole

theorem pairModel_childless (n : Nat) :
    ∀ v, ¬ pairModel.edge (3*n+2) v := by
  intro v h
  change v/3 = (3*n+2)/3+1 ∧ (3*n+2)%3 < 2 at h
  omega

theorem pairModel_no_descendants (n : Nat) :
    ∀ v, ¬ Descendant pairModel.edge (3*n+2) v := by
  intro v h
  induction h with
  | edge he => exact pairModel_childless n _ he
  | snoc _ _ ih => exact ih

end ExtinctionPedigree

#print axioms ExtinctionPedigree.Model.descendant_cut
#print axioms ExtinctionPedigree.Model.sync_resolves_cohort
#print axioms ExtinctionPedigree.Model.late_sync_resolves
#print axioms ExtinctionPedigree.Model.late_sync_every_subset_iap
#print axioms ExtinctionPedigree.Model.global_iap_iff_late_sync
#print axioms ExtinctionPedigree.Model.common_parents_sync
#print axioms ExtinctionPedigree.pairModel_late_sync
#print axioms ExtinctionPedigree.pairModel_iap
#print axioms ExtinctionPedigree.pairModel_childless
#print axioms ExtinctionPedigree.pairModel_no_descendants
