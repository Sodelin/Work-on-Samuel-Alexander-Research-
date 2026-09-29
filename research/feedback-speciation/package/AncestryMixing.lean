import SamuelAlexanderResearch.SpeciesGlobalIAP
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Max

/-!
Finite-community recurrence and Alexander's IAP predicate.
The finite-window local dissemination premise is strong and explicit.
This is a conditional pedigree theorem, not a biological species classifier.
No probability, cultural dynamics, or novelty claim is built into this file.
-/
namespace AncestryMixing
open SpeciesBridge SpeciesGlobalIAP

inductive Walk {D : Type} (R : D → D → Prop) : D → D → Prop where
  | refl (a : D) : Walk R a a
  | snoc {a b c : D} : Walk R a b → R b c → Walk R a c

theorem Walk.trans {D : Type} {R : D → D → Prop} {a b c : D}
    (hab : Walk R a b) (hbc : Walk R b c) : Walk R a c := by
  induction hbc with
  | refl => exact hab
  | snoc _ he ih => exact .snoc ih he

structure Pedigree (k : Nat) where
  edge : Graph
  generation : Nat → Nat
  deme : Nat → Fin k
  finitePast : ∀ n, FiniteSupport (fun v => generation v < n)
  occupied : ∀ n a, ∃ v, generation v = n ∧ deme v = a
  edgeStep : ∀ u v, edge u v → generation v = generation u + 1
  ownParent : ∀ v, 0 < generation v → ∃ u, edge u v ∧ deme u = deme v
  lag : Nat
  lagPositive : 0 < lag
  localMix : ∀ u v, generation v = generation u + lag → deme v = deme u →
    Descendant (fun x y => edge x y ∧ deme x = deme y) u v

namespace Pedigree

variable {k : Nat} (G : Pedigree k)

def Recurrent (a b : Fin k) : Prop :=
  ∀ N, ∃ u v, N ≤ G.generation u ∧ G.deme u = a ∧ G.deme v = b ∧ G.edge u v

def SameComponent (a b : Fin k) : Prop :=
  Walk G.Recurrent a b ∧ Walk G.Recurrent b a

def Saturates (u : Nat) (a : Fin k) : Prop :=
  ∃ N, ∀ v, N ≤ G.generation v → G.deme v = a → Descendant G.edge u v

def StronglyConnected : Prop := ∀ a b, Walk G.Recurrent a b

private theorem finite_uniform {D : Type} [Fintype D] (P : D → Nat → Prop)
    (h : ∀ d, ∃ n, P d n) : ∃ N, ∀ d, ∃ n, n ≤ N ∧ P d n := by
  classical
  let f : D → Nat := fun d => Classical.choose (h d)
  refine ⟨Finset.univ.sup f, ?_⟩
  intro d
  exact ⟨f d, Finset.le_sup (Finset.mem_univ d), Classical.choose_spec (h d)⟩

private theorem finite_iUnion_fin (P : Fin k → NatSet)
    (h : ∀ a, FiniteSupport (P a)) : FiniteSupport (fun v => ∃ a, P a v) := by
  classical
  have hb : ∀ a, ∃ n, ∀ v, P a v → v < n :=
    fun a => (finiteSupport_iff_bounded _).mp (h a)
  obtain ⟨N, hN⟩ := finite_uniform (fun a n => ∀ v, P a v → v < n) hb
  apply (finiteSupport_iff_bounded _).mpr
  refine ⟨N, ?_⟩
  intro v hv
  obtain ⟨a, ha⟩ := hv
  obtain ⟨n, hn, hbound⟩ := hN a
  exact Nat.lt_of_lt_of_le (hbound v ha) hn

private theorem mem_le_sum {xs : List Nat} {n : Nat} (h : n ∈ xs) : n ≤ xs.sum := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.mem_cons] at h
    simp only [List.sum_cons]
    rcases h with rfl | h
    · omega
    · have := ih h; omega

private theorem finite_generation_bound {S : NatSet} (hS : FiniteSupport S) :
    ∃ N, ∀ v, S v → G.generation v < N := by
  obtain ⟨xs, hxs⟩ := hS
  refine ⟨(xs.map G.generation).sum + 1, ?_⟩
  intro v hv
  have hmem : G.generation v ∈ xs.map G.generation :=
    List.mem_map.mpr ⟨v, hxs v hv, rfl⟩
  have := mem_le_sum hmem
  omega

theorem deme_infinite (a : Fin k) : InfiniteSupport (fun v => G.deme v = a) := by
  intro hfin
  obtain ⟨N, hN⟩ := G.finite_generation_bound hfin
  obtain ⟨v, hv, ha⟩ := G.occupied N a
  have := hN v ha
  omega

private theorem exists_late {S : NatSet} (hS : InfiniteSupport S) (N : Nat) :
    ∃ v, S v ∧ N ≤ G.generation v := by
  classical
  by_contra h
  apply hS
  apply finiteSupport_mono (T := fun v => G.generation v < N) ?_ (G.finitePast N)
  intro v hv
  by_contra hlt
  exact h ⟨v, hv, by omega⟩

private theorem local_descendant {u v : Nat}
    (h : Descendant (fun x y => G.edge x y ∧ G.deme x = G.deme y) u v) :
    Descendant G.edge u v := by
  induction h with
  | edge he => exact .edge he.1
  | snoc _ he ih => exact .snoc ih he.1

theorem descendant_generation_lt {u v : Nat} (h : Descendant G.edge u v) :
    G.generation u < G.generation v := by
  induction h with
  | edge he => have := G.edgeStep _ _ he; omega
  | snoc _ he ih => have := G.edgeStep _ _ he; omega

/-- The temporal persistence conclusion is proved from finite local windows. -/
theorem local_saturation_persists (u : Nat) : G.Saturates u (G.deme u) := by
  have hcover : ∀ m v, G.generation v = G.generation u + G.lag + m →
      G.deme v = G.deme u → Descendant G.edge u v := by
    intro m
    induction m with
    | zero =>
      intro v hv hd
      exact G.local_descendant (G.localMix u v (by simpa using hv) hd)
    | succ m ih =>
      intro v hv hd
      obtain ⟨p, hp, hpd⟩ := G.ownParent v (by have := G.lagPositive; omega)
      have hstep := G.edgeStep p v hp
      exact .snoc (ih p (by omega) (hpd.trans hd)) hp
  refine ⟨G.generation u + G.lag, ?_⟩
  intro v hv hd
  exact hcover (G.generation v - (G.generation u + G.lag)) v (by omega) hd

private theorem saturation_of_descendant {u v : Nat} {a : Fin k}
    (huv : Descendant G.edge u v) (hva : G.Saturates v a) : G.Saturates u a := by
  obtain ⟨N, hN⟩ := hva
  exact ⟨N, fun w hw hd => huv.trans (hN w hw hd)⟩

theorem saturation_crosses_recurrent_edge {u : Nat} {a b : Fin k}
    (hua : G.Saturates u a) (hab : G.Recurrent a b) : G.Saturates u b := by
  obtain ⟨N, hN⟩ := hua
  obtain ⟨x, y, hx, hxa, hyb, hxy⟩ := hab N
  have huy : Descendant G.edge u y := .snoc (hN x hx hxa) hxy
  have hy := G.local_saturation_persists y
  rw [hyb] at hy
  exact G.saturation_of_descendant huy hy

theorem saturation_of_recurrent_walk {u : Nat} {a b : Fin k}
    (hua : G.Saturates u a) (hab : Walk G.Recurrent a b) : G.Saturates u b := by
  induction hab with
  | refl => exact hua
  | snoc _ he ih => exact G.saturation_crosses_recurrent_edge ih he

/-- There is a single cutoff for all finitely many nonrecurrent edge types. -/
theorem exists_nonrecurrent_cutoff :
    ∃ T, ∀ u v, T ≤ G.generation u → G.edge u v → G.Recurrent (G.deme u) (G.deme v) := by
  classical
  let P (p : Fin k × Fin k) (T : Nat) :=
    ∀ u v, T ≤ G.generation u → G.deme u = p.1 → G.deme v = p.2 →
      G.edge u v → G.Recurrent p.1 p.2
  have hp : ∀ p, ∃ T, P p T := by
    intro p
    by_cases hr : G.Recurrent p.1 p.2
    · exact ⟨0, fun _ _ _ _ _ _ => hr⟩
    · change ¬ (∀ N, ∃ u v, N ≤ G.generation u ∧ G.deme u = p.1 ∧
        G.deme v = p.2 ∧ G.edge u v) at hr
      obtain ⟨T, hT⟩ := not_forall.mp hr
      exact ⟨T, fun u v hu hdu hdv he => False.elim (hT ⟨u, v, hu, hdu, hdv, he⟩)⟩
  obtain ⟨T, hT⟩ := finite_uniform P hp
  refine ⟨T, ?_⟩
  intro u v hu he
  obtain ⟨n, hn, hN⟩ := hT (G.deme u, G.deme v)
  exact hN u v (Nat.le_trans hn hu) rfl rfl he

theorem late_descendant_projects {T : Nat}
    (hT : ∀ u v, T ≤ G.generation u → G.edge u v → G.Recurrent (G.deme u) (G.deme v))
    {u v : Nat} (hu : T ≤ G.generation u) (h : Descendant G.edge u v) :
    Walk G.Recurrent (G.deme u) (G.deme v) := by
  induction h with
  | edge he => exact .snoc (.refl _) (hT _ _ hu he)
  | snoc hpath he ih =>
    have hg := G.descendant_generation_lt hpath
    exact .snoc ih (hT _ _ (by omega) he)

/-- Exact late ancestry is derived, rather than assumed as an interface. -/
theorem eventual_descendant_iff_recurrent_reach :
    ∃ T, ∀ u, T ≤ G.generation u → ∃ N, ∀ v, N ≤ G.generation v →
      (Descendant G.edge u v ↔ Walk G.Recurrent (G.deme u) (G.deme v)) := by
  classical
  obtain ⟨T, hT⟩ := G.exists_nonrecurrent_cutoff
  refine ⟨T, ?_⟩
  intro u hu
  let P (a : Fin k) (N : Nat) := Walk G.Recurrent (G.deme u) a →
    ∀ v, N ≤ G.generation v → G.deme v = a → Descendant G.edge u v
  have hp : ∀ a, ∃ N, P a N := by
    intro a
    by_cases ha : Walk G.Recurrent (G.deme u) a
    · obtain ⟨N, hN⟩ := G.saturation_of_recurrent_walk (G.local_saturation_persists u) ha
      exact ⟨N, fun _ => hN⟩
    · exact ⟨0, fun h => False.elim (ha h)⟩
  obtain ⟨N, hN⟩ := finite_uniform P hp
  refine ⟨N, ?_⟩
  intro v hv
  constructor
  · exact G.late_descendant_projects hT hu
  · intro h
    obtain ⟨n, hn, hbound⟩ := hN (G.deme v)
    exact hbound h v (Nat.le_trans hn hv) rfl

private theorem finite_nondescendants_of_saturation (u : Nat) (A : Fin k → Prop)
    (hsat : ∀ a, A a → G.Saturates u a) :
    FiniteSupport (fun v => A (G.deme v) ∧ ¬ Descendant G.edge u v) := by
  classical
  let P (a : Fin k) (v : Nat) := G.deme v = a ∧ A a ∧ ¬ Descendant G.edge u v
  have hp : ∀ a, FiniteSupport (P a) := by
    intro a
    by_cases ha : A a
    · obtain ⟨N, hN⟩ := hsat a ha
      apply finiteSupport_mono (T := fun v => G.generation v < N) ?_ (G.finitePast N)
      intro v hv
      by_contra hlt
      exact hv.2.2 (hN v (by omega) hv.1)
    · exact ⟨[], fun _ hv => False.elim (ha hv.2.1)⟩
  apply finiteSupport_mono (T := fun v => ∃ a, P a v) ?_ (finite_iUnion_fin P hp)
  intro v hv
  exact ⟨G.deme v, rfl, hv⟩

private theorem infinite_deme_of_infinite {S : NatSet} (hS : InfiniteSupport S) :
    ∃ a, InfiniteSupport (fun v => S v ∧ G.deme v = a) := by
  classical
  by_contra h
  have hf : ∀ a, FiniteSupport (fun v => S v ∧ G.deme v = a) := by
    intro a
    exact Classical.byContradiction (fun hna => h ⟨a, hna⟩)
  apply hS
  exact finiteSupport_mono (fun v hv => ⟨G.deme v, hv, rfl⟩)
    (finite_iUnion_fin (fun a v => S v ∧ G.deme v = a) hf)

private theorem not_iap_of_two_infinite_demes {S : NatSet} {a b : Fin k} {T : Nat}
    (hT : ∀ u v, T ≤ G.generation u → G.edge u v → G.Recurrent (G.deme u) (G.deme v))
    (ha : InfiniteSupport (fun v => S v ∧ G.deme v = a))
    (hb : InfiniteSupport (fun v => S v ∧ G.deme v = b))
    (hab : ¬ Walk G.Recurrent a b) : ¬ IAP G.edge S := by
  obtain ⟨v, hv, hlate⟩ := G.exists_late ha T
  have hsat := G.local_saturation_persists v
  rw [hv.2] at hsat
  obtain ⟨N, hN⟩ := hsat
  intro hiap
  rcases hiap v hv.1 with hdesc | hnon
  · apply ha
    apply finiteSupport_mono
      (T := fun w => (S w ∧ Descendant G.edge v w) ∨ G.generation w < N) ?_
      (finiteSupport_union hdesc (G.finitePast N))
    intro w hw
    by_cases hn : N ≤ G.generation w
    · exact Or.inl ⟨hw.1, hN w hn hw.2⟩
    · exact Or.inr (by omega)
  · apply hb
    apply finiteSupport_mono ?_ hnon
    intro w hw
    refine ⟨hw.1, ?_⟩
    intro hvw
    have hp := G.late_descendant_projects hT hlate hvw
    rw [hv.2, hw.2] at hp
    exact hab hp

/-- The SCC characterization uses actual Alexander IAP and standard finiteness. -/
theorem iap_iff_one_recurrent_component_mod_finite (S : NatSet) (hS : InfiniteSupport S) :
    IAP G.edge S ↔ ∃ a, FiniteSupport (fun v => S v ∧ ¬ G.SameComponent a (G.deme v)) := by
  classical
  constructor
  · intro hiap
    obtain ⟨T, hT⟩ := G.exists_nonrecurrent_cutoff
    obtain ⟨a, ha⟩ := G.infinite_deme_of_infinite hS
    refine ⟨a, ?_⟩
    let P (b : Fin k) (v : Nat) := S v ∧ G.deme v = b ∧ ¬ G.SameComponent a b
    have hp : ∀ b, FiniteSupport (P b) := by
      intro b
      by_cases hab : G.SameComponent a b
      · exact ⟨[], fun _ hv => False.elim (hv.2.2 hab)⟩
      · have hb : FiniteSupport (fun v => S v ∧ G.deme v = b) := by
          apply Classical.byContradiction
          intro hnb
          by_cases hab' : Walk G.Recurrent a b
          · have hba : ¬ Walk G.Recurrent b a := fun h => hab ⟨hab', h⟩
            exact G.not_iap_of_two_infinite_demes hT hnb ha hba hiap
          · exact G.not_iap_of_two_infinite_demes hT ha hnb hab' hiap
        exact finiteSupport_mono (fun _ hv => ⟨hv.1, hv.2.1⟩) hb
    apply finiteSupport_mono (T := fun v => ∃ b, P b v) ?_ (finite_iUnion_fin P hp)
    intro v hv
    exact ⟨G.deme v, hv.1, rfl, hv.2⟩
  · rintro ⟨a, houtside⟩ v hv
    by_cases hentry : ∃ z, G.SameComponent a (G.deme z) ∧ Descendant G.edge v z
    · obtain ⟨z, hz, hvz⟩ := hentry
      have hsat : ∀ b, G.SameComponent a b → G.Saturates v b := by
        intro b hb
        have hzb : Walk G.Recurrent (G.deme z) b := hz.2.trans hb.1
        exact G.saturation_of_descendant hvz
          (G.saturation_of_recurrent_walk (G.local_saturation_persists z) hzb)
      have hf := G.finite_nondescendants_of_saturation v (G.SameComponent a) hsat
      apply Or.inr
      apply finiteSupport_mono
        (T := fun w => (S w ∧ ¬ G.SameComponent a (G.deme w)) ∨
          (G.SameComponent a (G.deme w) ∧ ¬ Descendant G.edge v w)) ?_
        (finiteSupport_union houtside hf)
      intro w hw
      by_cases hc : G.SameComponent a (G.deme w)
      · exact Or.inr ⟨hc, hw.2⟩
      · exact Or.inl ⟨hw.1, hc⟩
    · apply Or.inl
      apply finiteSupport_mono ?_ houtside
      intro w hw
      exact ⟨hw.1, fun hc => hentry ⟨w, hc, hw.2⟩⟩

/-- Recurrent strong connectivity forces cofinite ancestry for every organism. -/
theorem cofinite_descendants_of_recurrent_strongly_connected (h : G.StronglyConnected) :
    CofiniteDescendants G.edge := by
  intro v
  have hs : ∀ a, True → G.Saturates v a :=
    fun a _ => G.saturation_of_recurrent_walk (G.local_saturation_persists v) (h _ a)
  exact finiteSupport_mono (fun _ hw => ⟨trivial, hw⟩)
    (G.finite_nondescendants_of_saturation v (fun _ => True) hs)

theorem whole_iap_iff_recurrent_strongly_connected :
    IAP G.edge Whole ↔ G.StronglyConnected := by
  classical
  constructor
  · intro hiap
    obtain ⟨a, ha⟩ := (G.iap_iff_one_recurrent_component_mod_finite Whole whole_infinite).mp hiap
    have hall : ∀ b, G.SameComponent a b := by
      intro b
      by_contra hb
      apply G.deme_infinite b
      apply finiteSupport_mono ?_ ha
      intro v hv
      exact ⟨trivial, by simpa [hv] using hb⟩
    intro b c
    exact (hall b).2.trans (hall c).1
  · intro h
    apply (iap_whole_iff G.edge).mpr
    intro v
    exact Or.inr (G.cofinite_descendants_of_recurrent_strongly_connected h v)

theorem whole_inspecies_of_recurrent_strongly_connected (h : G.StronglyConnected) :
    Inspecies G.edge Whole :=
  (whole_inspecies_iff_cofinite_descendants G.edge).mpr
    (G.cofinite_descendants_of_recurrent_strongly_connected h)

/-- All organisms in one recurrent component born at or after a cutoff. -/
def ComponentTail (a : Fin k) (T : Nat) : NatSet :=
  fun v => T ≤ G.generation v ∧ G.SameComponent a (G.deme v)

theorem component_tail_infinite (a : Fin k) (T : Nat) :
    InfiniteSupport (G.ComponentTail a T) := by
  intro hfin
  obtain ⟨N, hN⟩ := G.finite_generation_bound hfin
  obtain ⟨v, hv, hd⟩ := G.occupied (N + T) a
  have hmem : G.ComponentTail a T v := by
    refine ⟨by omega, ?_⟩
    rw [hd]
    exact ⟨.refl a, .refl a⟩
  have := hN v hmem
  omega

theorem component_tail_cofinite_descendants (a : Fin k) (T : Nat)
    {v : Nat} (hv : G.ComponentTail a T v) :
    FiniteSupport (fun w => G.ComponentTail a T w ∧ ¬ Descendant G.edge v w) := by
  have hsat : ∀ b, G.SameComponent a b → G.Saturates v b := by
    intro b hb
    exact G.saturation_of_recurrent_walk (G.local_saturation_persists v)
      (hv.2.2.trans hb.1)
  exact finiteSupport_mono (fun _ hw => ⟨hw.1.2, hw.2⟩)
    (G.finite_nondescendants_of_saturation v (G.SameComponent a) hsat)

theorem component_tail_infinite_descendants (a : Fin k) (T : Nat)
    {v : Nat} (hv : G.ComponentTail a T v) :
    InfiniteSupport (fun w => G.ComponentTail a T w ∧ Descendant G.edge v w) := by
  classical
  intro hfin
  apply G.component_tail_infinite a T
  apply finiteSupport_mono (T := fun w =>
    (G.ComponentTail a T w ∧ Descendant G.edge v w) ∨
    (G.ComponentTail a T w ∧ ¬ Descendant G.edge v w)) ?_
    (finiteSupport_union hfin (G.component_tail_cofinite_descendants a T hv))
  intro w hw
  by_cases hd : Descendant G.edge v w
  · exact Or.inl ⟨hw, hd⟩
  · exact Or.inr ⟨hw, hd⟩

theorem component_tail_convex {T : Nat}
    (hT : ∀ u v, T ≤ G.generation u → G.edge u v → G.Recurrent (G.deme u) (G.deme v))
    (a : Fin k) : Convex G.edge (G.ComponentTail a T) := by
  rintro v ⟨u, hu, huv⟩ ⟨w, hw, hvw⟩
  have hgen := G.descendant_generation_lt huv
  have hvlate : T ≤ G.generation v := by have := hu.1; omega
  have hleft := G.late_descendant_projects hT hu.1 huv
  have hright := G.late_descendant_projects hT hvlate hvw
  exact ⟨hvlate, hu.2.1.trans hleft, hright.trans hw.2.2⟩

private theorem descendant_weakReach_of_convex {E : Graph} {S : NatSet}
    (hc : Convex E S) {u v : Nat} (hu : S u) (hpath : Descendant E u v) :
    S v → WeakReach E S u v := by
  induction hpath with
  | edge he => intro hv; exact .edge hu hv (Or.inl he)
  | snoc hpath he ih =>
    intro hv
    have hm := hc _ ⟨_, hu, hpath⟩ ⟨_, hv, .edge he⟩
    exact .trans (ih hm) (.edge hm hv (Or.inl he))

theorem component_tail_weaklyConnected {T : Nat}
    (hT : ∀ u v, T ≤ G.generation u → G.edge u v → G.Recurrent (G.deme u) (G.deme v))
    (a : Fin k) : WeaklyConnected G.edge (G.ComponentTail a T) := by
  have hc := G.component_tail_convex hT a
  obtain ⟨z, hz, hd⟩ := G.occupied T a
  refine ⟨⟨z, ?_⟩, ?_⟩
  · refine ⟨by omega, ?_⟩
    rw [hd]
    exact ⟨.refl a, .refl a⟩
  · intro u v hu hv
    obtain ⟨Nu, hNu⟩ := G.saturation_of_recurrent_walk
      (G.local_saturation_persists u) hu.2.2
    obtain ⟨Nv, hNv⟩ := G.saturation_of_recurrent_walk
      (G.local_saturation_persists v) hv.2.2
    obtain ⟨w, hw, hwd⟩ := G.occupied (T + Nu + Nv) a
    have hwm : G.ComponentTail a T w := by
      refine ⟨by omega, ?_⟩
      rw [hwd]
      exact ⟨.refl a, .refl a⟩
    have huw := hNu w (by omega) hwd
    have hvw := hNv w (by omega) hwd
    exact .trans (descendant_weakReach_of_convex hc hu huw hwm)
      (descendant_weakReach_of_convex hc hv hvw hwm).symm

/-- One common cutoff gives actual specieslike reflecting tails for every SCC. -/
theorem recurrent_component_tails_specieslike_reflection :
    ∃ T, ∀ a, InfiniteSupport (G.ComponentTail a T) ∧
      Specieslike G.edge (G.ComponentTail a T) ∧
      Reflection G.edge (G.ComponentTail a T) := by
  obtain ⟨T, hT⟩ := G.exists_nonrecurrent_cutoff
  refine ⟨T, ?_⟩
  intro a
  refine ⟨G.component_tail_infinite a T, ?_, ?_⟩
  · exact ⟨G.component_tail_weaklyConnected hT a,
      fun _ hv => Or.inr (G.component_tail_cofinite_descendants a T hv),
      G.component_tail_convex hT a⟩
  · intro v hv _
    exact G.component_tail_infinite_descendants a T hv

end Pedigree

end AncestryMixing

#print axioms AncestryMixing.Pedigree.local_saturation_persists
#print axioms AncestryMixing.Pedigree.saturation_crosses_recurrent_edge
#print axioms AncestryMixing.Pedigree.exists_nonrecurrent_cutoff
#print axioms AncestryMixing.Pedigree.late_descendant_projects
#print axioms AncestryMixing.Pedigree.eventual_descendant_iff_recurrent_reach
#print axioms AncestryMixing.Pedigree.iap_iff_one_recurrent_component_mod_finite
#print axioms AncestryMixing.Pedigree.cofinite_descendants_of_recurrent_strongly_connected
#print axioms AncestryMixing.Pedigree.whole_iap_iff_recurrent_strongly_connected
#print axioms AncestryMixing.Pedigree.whole_inspecies_of_recurrent_strongly_connected

#print axioms AncestryMixing.Pedigree.recurrent_component_tails_specieslike_reflection
