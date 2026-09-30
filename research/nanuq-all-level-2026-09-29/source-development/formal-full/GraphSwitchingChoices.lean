import GraphSwitchingFinite

/-! Actual global switchings are exactly independent incoming-edge choices at
hybrids. Partial choices extend by default choices; no graph decomposition,
quartet identity, or metric property is an input. -/
namespace Nanuq.Source.RootedBinary

variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

def Hybrid := {a : V // N.graph.IsHybrid a}

def IncomingChoice (h : N.Hybrid) := {e : E // N.graph.target e = h.val}

abbrev HybridChoices := (h : N.Hybrid) → N.IncomingChoice h

noncomputable instance hybridFintype : Fintype N.Hybrid := by
  classical
  unfold Hybrid
  infer_instance

noncomputable instance incomingChoiceFintype (h : N.Hybrid) : Fintype (N.IncomingChoice h) := by
  classical
  unfold IncomingChoice
  infer_instance

/-- Extract the unique retained actual incoming edge at each hybrid. -/
noncomputable def choicesOfSwitching (S : N.Switching) : N.HybridChoices := fun h =>
  ⟨Classical.choose (S.hybrid_unique h.val h.property),
    (Classical.choose_spec (S.hybrid_unique h.val h.property)).1⟩

theorem choicesOfSwitching_kept (S : N.Switching) (h : N.Hybrid) :
    S.keep (N.choicesOfSwitching S h).val :=
  (Classical.choose_spec (S.hybrid_unique h.val h.property)).2.1

theorem choicesOfSwitching_unique (S : N.Switching) (h : N.Hybrid) (e : E)
    (he : N.graph.target e = h.val) (hk : S.keep e) :
    e = (N.choicesOfSwitching S h).val :=
  (Classical.choose_spec (S.hybrid_unique h.val h.property)).2.2 e he hk

theorem switching_keep_iff_choices (S : N.Switching) (e : E) :
    S.keep e ↔ ¬ N.graph.IsHybrid (N.graph.target e) ∨
      ∃ h : N.Hybrid, (N.choicesOfSwitching S h).val = e := by
  constructor
  · intro hk
    by_cases hh : N.graph.IsHybrid (N.graph.target e)
    · right
      let h : N.Hybrid := ⟨N.graph.target e,hh⟩
      exact ⟨h,(N.choicesOfSwitching_unique S h e rfl hk).symm⟩
    · exact Or.inl hh
  · rintro (hh | ⟨h,he⟩)
    · exact S.ordinary e hh
    · rw [← he]
      exact N.choicesOfSwitching_kept S h

/-- Build the actual retained-edge switching from arbitrary actual incoming
choices. Ordinary edges are retained, and each hybrid retains precisely its choice. -/
def switchingOfChoices (C : N.HybridChoices) : N.Switching where
  keep e := ¬ N.graph.IsHybrid (N.graph.target e) ∨ ∃ h : N.Hybrid, (C h).val = e
  ordinary _ hh := Or.inl hh
  hybrid_unique a ha := by
    let h : N.Hybrid := ⟨a,ha⟩
    refine ⟨(C h).val,(C h).property,Or.inr ⟨h,rfl⟩,?_⟩
    intro f hf hk
    rcases hk with hh | ⟨j,hj⟩
    · exact False.elim (hh (hf ▸ ha))
    · have hv : j.val = a := by rw [← (C j).property,hj,hf]
      have he : j = h := Subtype.ext hv
      rw [he] at hj
      exact hj.symm

theorem switchingOfChoices_keep_at_hybrid (C : N.HybridChoices) (h : N.Hybrid)
    (e : E) (he : N.graph.target e = h.val) :
    (N.switchingOfChoices C).keep e ↔ e = (C h).val := by
  constructor
  · rintro (hh | ⟨j,hj⟩)
    · exact False.elim (hh (he ▸ h.property))
    · have hv : j.val = h.val := by rw [← (C j).property,hj,he]
      have heq : j = h := Subtype.ext hv
      rw [heq] at hj
      exact hj.symm
  · intro hh
    exact Or.inr ⟨h,hh.symm⟩

@[simp] theorem choicesOfSwitching_switchingOfChoices (C : N.HybridChoices) :
    N.choicesOfSwitching (N.switchingOfChoices C) = C := by
  funext h
  apply Subtype.ext
  exact (N.choicesOfSwitching_unique (N.switchingOfChoices C) h (C h).val
    (C h).property (Or.inr ⟨h,rfl⟩)).symm

@[simp] theorem switchingOfChoices_choicesOfSwitching (S : N.Switching) :
    N.switchingOfChoices (N.choicesOfSwitching S) = S := by
  apply Switching.keep_injective N
  funext e
  apply propext
  exact (N.switching_keep_iff_choices S e).symm

/-- Exact equivalence, not only existence of a switching from choices. -/
noncomputable def switchingChoicesEquiv : N.Switching ≃ N.HybridChoices where
  toFun := N.choicesOfSwitching
  invFun := N.switchingOfChoices
  left_inv := N.switchingOfChoices_choicesOfSwitching
  right_inv := N.choicesOfSwitching_switchingOfChoices

noncomputable def defaultHybridChoices : N.HybridChoices :=
  N.choicesOfSwitching N.defaultSwitching

abbrev PartialHybridChoices (P : N.Hybrid → Prop) :=
  (h : {h : N.Hybrid // P h}) → N.IncomingChoice h.val

def restrictHybridChoices (P : N.Hybrid → Prop) (C : N.HybridChoices) :
    N.PartialHybridChoices P := fun h => C h.val

/-- Choices outside a specified subset are filled with the already constructed
actual default switching. No compatibility assumption is needed. -/
noncomputable def extendHybridChoices (P : N.Hybrid → Prop) (C : N.PartialHybridChoices P) :
    N.HybridChoices := by
  classical
  exact fun h => if hp : P h then C ⟨h,hp⟩ else N.defaultHybridChoices h

@[simp] theorem extendHybridChoices_on (P : N.Hybrid → Prop) (C : N.PartialHybridChoices P)
    (h : N.Hybrid) (hp : P h) : N.extendHybridChoices P C h = C ⟨h,hp⟩ := by
  simp [extendHybridChoices,hp]

@[simp] theorem extendHybridChoices_off (P : N.Hybrid → Prop) (C : N.PartialHybridChoices P)
    (h : N.Hybrid) (hp : ¬ P h) : N.extendHybridChoices P C h = N.defaultHybridChoices h := by
  simp [extendHybridChoices,hp]

@[simp] theorem restrict_extendHybridChoices (P : N.Hybrid → Prop)
    (C : N.PartialHybridChoices P) :
    N.restrictHybridChoices P (N.extendHybridChoices P C) = C := by
  funext h
  exact N.extendHybridChoices_on P C h.val h.property

theorem restrictHybridChoices_surjective (P : N.Hybrid → Prop) :
    Function.Surjective (N.restrictHybridChoices P) := by
  intro C
  exact ⟨N.extendHybridChoices P C,N.restrict_extendHybridChoices P C⟩

noncomputable def restrictSwitchingChoices (P : N.Hybrid → Prop) (S : N.Switching) :
    N.PartialHybridChoices P := N.restrictHybridChoices P (N.choicesOfSwitching S)

/-- Every prescribed set of local hybrid-edge choices is attained by an actual
global switching. This is the extension map needed for blob restrictions. -/
theorem restrictSwitchingChoices_surjective (P : N.Hybrid → Prop) :
    Function.Surjective (N.restrictSwitchingChoices P) := by
  intro C
  refine ⟨N.switchingOfChoices (N.extendHybridChoices P C),?_⟩
  simp only [restrictSwitchingChoices,choicesOfSwitching_switchingOfChoices,
    restrict_extendHybridChoices]

theorem extended_switching_keep_on (P : N.Hybrid → Prop) (C : N.PartialHybridChoices P)
    (h : N.Hybrid) (hp : P h) (e : E) (he : N.graph.target e = h.val) :
    (N.switchingOfChoices (N.extendHybridChoices P C)).keep e ↔ e = (C ⟨h,hp⟩).val := by
  rw [switchingOfChoices_keep_at_hybrid N _ h e he,extendHybridChoices_on N P C h hp]

theorem extended_switching_keep_off (P : N.Hybrid → Prop) (C : N.PartialHybridChoices P)
    (h : N.Hybrid) (hp : ¬ P h) (e : E) (he : N.graph.target e = h.val) :
    (N.switchingOfChoices (N.extendHybridChoices P C)).keep e ↔ N.defaultSwitching.keep e := by
  rw [switchingOfChoices_keep_at_hybrid N _ h e he,extendHybridChoices_off N P C h hp]
  change e = (N.choicesOfSwitching N.defaultSwitching h).val ↔ N.defaultSwitching.keep e
  constructor
  · intro hh
    rw [hh]
    exact N.choicesOfSwitching_kept N.defaultSwitching h
  · exact N.choicesOfSwitching_unique N.defaultSwitching h e he


noncomputable instance hybridSubsetFintype (P : N.Hybrid → Prop) :
    Fintype {h : N.Hybrid // P h} := by
  classical
  infer_instance

instance partialHybridChoicesNonempty (P : N.Hybrid → Prop) :
    Nonempty (N.PartialHybridChoices P) :=
  ⟨N.restrictHybridChoices P N.defaultHybridChoices⟩

/-- Independent choices on a subset and its complement reconstruct all choices.
This equivalence also retains the counting information needed for uniform
switching averages, which a bare surjectivity theorem would not supply. -/
noncomputable def hybridChoicesSplitEquiv (P : N.Hybrid → Prop) :
    N.HybridChoices ≃ N.PartialHybridChoices P × N.PartialHybridChoices (fun h => ¬ P h) := by
  classical
  refine {
    toFun := fun C => (N.restrictHybridChoices P C,N.restrictHybridChoices (fun h => ¬ P h) C)
    invFun := fun CD h => if hp : P h then CD.1 ⟨h,hp⟩ else CD.2 ⟨h,hp⟩
    left_inv := ?_
    right_inv := ?_
  }
  · intro C
    funext h
    by_cases hp : P h <;> simp [restrictHybridChoices,hp]
  · intro CD
    apply Prod.ext
    · funext h
      simp [restrictHybridChoices,h.property]
    · funext h
      simp [restrictHybridChoices,h.property]

noncomputable def switchingSplitChoicesEquiv (P : N.Hybrid → Prop) :
    N.Switching ≃ N.PartialHybridChoices P × N.PartialHybridChoices (fun h => ¬ P h) :=
  N.switchingChoicesEquiv.trans (N.hybridChoicesSplitEquiv P)

@[simp] theorem switchingSplitChoicesEquiv_fst (P : N.Hybrid → Prop) (S : N.Switching) :
    (N.switchingSplitChoicesEquiv P S).1 = N.restrictSwitchingChoices P S := rfl

@[simp] theorem switchingSplitChoicesEquiv_snd (P : N.Hybrid → Prop) (S : N.Switching) :
    (N.switchingSplitChoicesEquiv P S).2 = N.restrictSwitchingChoices (fun h => ¬ P h) S := rfl

#print axioms switchingSplitChoicesEquiv
#print axioms switchingChoicesEquiv
#print axioms restrictSwitchingChoices_surjective
#print axioms extended_switching_keep_on
#print axioms extended_switching_keep_off
end Nanuq.Source.RootedBinary


