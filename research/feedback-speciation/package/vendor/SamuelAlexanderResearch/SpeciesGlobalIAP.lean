import SamuelAlexanderResearch.SpeciesBridge

/-!
# Global IAP, reflection, and whole-graph inspecies

The graph has vertex set `Nat`, so its ambient vertex set is infinite. No
birthdates, acyclicity, root bound, or child bound are assumed in the generic
results. Descendants are the nonempty directed paths of `SpeciesBridge`.

These are direct deductions from the species definitions, not priority claims.
The definition of inspecies below is inclusion-minimality among infinite,
ancestrally closed subsets, as in Alexander (2013), Definitions 3 and 4.
-/

namespace SpeciesGlobalIAP

open SpeciesBridge

theorem finiteSupport_singleton (v : Nat) :
    FiniteSupport (fun w => w = v) := by
  refine ⟨[v], ?_⟩
  intro w hw
  simpa only [List.mem_singleton] using hw

theorem finiteSupport_union {S T : NatSet}
    (hS : FiniteSupport S) (hT : FiniteSupport T) :
    FiniteSupport (fun w => S w ∨ T w) := by
  obtain ⟨xs, hxs⟩ := hS
  obtain ⟨ys, hys⟩ := hT
  refine ⟨xs ++ ys, ?_⟩
  intro w hw
  exact List.mem_append.mpr (hw.elim (fun hs => Or.inl (hxs w hs))
    (fun ht => Or.inr (hys w ht)))

theorem infiniteSupport_mono {S T : NatSet}
    (hST : ∀ w, S w → T w) (hS : InfiniteSupport S) :
    InfiniteSupport T := by
  intro hT
  exact hS (finiteSupport_mono hST hT)

/-- Every vertex has either finitely many descendants or finitely many
non-descendants in the ambient graph. -/
def FiniteOrCofiniteDescendants (E : Graph) : Prop :=
  ∀ v, FiniteSupport (Descendant E v) ∨
    FiniteSupport (fun w => ¬ Descendant E v w)

/-- Every vertex has cofinite strict descendants in the ambient graph. -/
def CofiniteDescendants (E : Graph) : Prop :=
  ∀ v, FiniteSupport (fun w => ¬ Descendant E v w)

theorem iap_whole_iff (E : Graph) :
    IAP E Whole ↔ FiniteOrCofiniteDescendants E := by
  constructor
  · intro h v
    rcases h v trivial with hd | hn
    · exact Or.inl (finiteSupport_mono (fun _ hw => ⟨trivial, hw⟩) hd)
    · exact Or.inr (finiteSupport_mono (fun _ hw => ⟨trivial, hw⟩) hn)
  · intro h v _
    rcases h v with hd | hn
    · exact Or.inl (finiteSupport_mono (fun _ hw => hw.2) hd)
    · exact Or.inr (finiteSupport_mono (fun _ hw => hw.2) hn)

theorem all_subsets_iap_iff (E : Graph) :
    (∀ S : NatSet, IAP E S) ↔ FiniteOrCofiniteDescendants E := by
  constructor
  · intro h
    exact (iap_whole_iff E).mp (h Whole)
  · intro h S v _
    rcases h v with hd | hn
    · exact Or.inl (finiteSupport_mono (fun _ hw => hw.2) hd)
    · exact Or.inr (finiteSupport_mono (fun _ hw => hw.2) hn)

theorem all_infinite_subsets_reflection_iff (E : Graph) :
    (∀ S : NatSet, InfiniteSupport S → Reflection E S) ↔
      FiniteOrCofiniteDescendants E := by
  classical
  constructor
  · intro h v
    by_cases hd : FiniteSupport (Descendant E v)
    · exact Or.inl hd
    · apply Or.inr
      by_cases hn : FiniteSupport (fun w => ¬ Descendant E v w)
      · exact hn
      · have hinf : InfiniteSupport (fun w => w = v ∨ ¬ Descendant E v w) :=
          infiniteSupport_mono (fun _ hw => Or.inr hw) hn
        have href := h _ hinf v (Or.inl rfl) hd
        apply False.elim
        apply href
        apply finiteSupport_mono (T := fun w => w = v) _ (finiteSupport_singleton v)
        intro w hw
        rcases hw.1 with heq | hnot
        · exact heq
        · exact False.elim (hnot hw.2)
  · intro h S hS v _ hdesc hfin
    rcases h v with hd | hn
    · exact hdesc hd
    · apply hS
      apply finiteSupport_mono (T := fun w => (S w ∧ Descendant E v w) ∨
        ¬ Descendant E v w) _ (finiteSupport_union hfin hn)
      intro w hw
      by_cases hDw : Descendant E v w
      · exact Or.inl ⟨hw, hDw⟩
      · exact Or.inr hDw

/-- The two quantified subset conditions are exactly equivalent. -/
theorem all_subsets_iap_iff_all_infinite_subsets_reflection (E : Graph) :
    (∀ S : NatSet, IAP E S) ↔
      (∀ S : NatSet, InfiniteSupport S → Reflection E S) :=
  (all_subsets_iap_iff E).trans (all_infinite_subsets_reflection_iff E).symm

/-- A whole-graph specieslike condition reduces to connectivity and the
finite-or-cofinite descendant dichotomy; whole-graph convexity is automatic. -/
theorem whole_specieslike_iff (E : Graph) :
    Specieslike E Whole ↔
      WeaklyConnected E Whole ∧ FiniteOrCofiniteDescendants E := by
  constructor
  · intro h
    exact ⟨h.1, (iap_whole_iff E).mp h.2.1⟩
  · rintro ⟨hconn, hiap⟩
    exact ⟨hconn, (iap_whole_iff E).mpr hiap, whole_convex E⟩

/-- Containment of a vertex entails containment of every strict ancestor. -/
def AncestrallyClosed (E : Graph) (S : NatSet) : Prop :=
  ∀ u v, S v → Descendant E u v → S u

/-- An infinitary genus is an infinite ancestrally closed vertex set. -/
def InfinitaryGenus (E : Graph) (S : NatSet) : Prop :=
  InfiniteSupport S ∧ AncestrallyClosed E S

/-- An inspecies is an inclusion-minimal infinitary genus. -/
def Inspecies (E : Graph) (S : NatSet) : Prop :=
  InfinitaryGenus E S ∧ ∀ T : NatSet,
    (∀ v, T v → S v) → InfinitaryGenus E T → ∀ v, S v → T v

theorem whole_ancestrallyClosed (E : Graph) : AncestrallyClosed E Whole := by
  intro _ _ _ _
  trivial

theorem whole_inspecies_iff_cofinite_descendants (E : Graph) :
    Inspecies E Whole ↔ CofiniteDescendants E := by
  classical
  constructor
  · intro h v
    by_cases hfin : FiniteSupport (fun w => ¬ Descendant E v w)
    · exact hfin
    · let S : NatSet := fun w => w ≠ v ∧ ¬ Descendant E v w
      have hinf : InfiniteSupport S := by
        intro hS
        apply hfin
        apply finiteSupport_mono (T := fun w => S w ∨ w = v) _
          (finiteSupport_union hS (finiteSupport_singleton v))
        intro w hw
        by_cases heq : w = v
        · exact Or.inr heq
        · exact Or.inl ⟨heq, hw⟩
      have hclosed : AncestrallyClosed E S := by
        intro u w hw huw
        constructor
        · intro huv
          subst u
          exact hw.2 huw
        · intro hvu
          exact hw.2 (hvu.trans huw)
      have hv := h.2 S (fun _ _ => trivial) ⟨hinf, hclosed⟩ v trivial
      exact False.elim (hv.1 rfl)
  · intro h
    refine ⟨⟨whole_infinite, whole_ancestrallyClosed E⟩, ?_⟩
    intro S _ hS v _
    by_cases hv : S v
    · exact hv
    · apply False.elim
      apply hS.1
      apply finiteSupport_mono (T := fun w => ¬ Descendant E v w) _ (h v)
      intro w hw hvw
      exact hv (hS.2 v w hw hvw)

theorem finiteOrCofinite_iff_cofinite_of_infinite_descendants (E : Graph)
    (hinf : ∀ v, InfiniteSupport (Descendant E v)) :
    FiniteOrCofiniteDescendants E ↔ CofiniteDescendants E := by
  constructor
  · intro h v
    rcases h v with hfin | hcofin
    · exact False.elim (hinf v hfin)
    · exact hcofin
  · intro h v
    exact Or.inr (h v)

theorem whole_iap_iff_inspecies_of_infinite_descendants (E : Graph)
    (hinf : ∀ v, InfiniteSupport (Descendant E v)) :
    IAP E Whole ↔ Inspecies E Whole :=
  (iap_whole_iff E).trans
    ((finiteOrCofinite_iff_cofinite_of_infinite_descendants E hinf).trans
      (whole_inspecies_iff_cofinite_descendants E).symm)

theorem reflection_iff_empty_or_infinite (E : Graph)
    (hglobal : FiniteOrCofiniteDescendants E)
    (hdesc : ∀ v, InfiniteSupport (Descendant E v)) (S : NatSet) :
    Reflection E S ↔ (∀ v, ¬ S v) ∨ InfiniteSupport S := by
  classical
  constructor
  · intro h
    by_cases hinf : InfiniteSupport S
    · exact Or.inr hinf
    · apply Or.inl
      intro v hv
      have hfin : FiniteSupport S := Classical.byContradiction hinf
      exact h v hv (hdesc v) (finiteSupport_mono (fun _ hw => hw.1) hfin)
  · rintro (hempty | hinf)
    · intro v hv
      exact False.elim (hempty v hv)
    · exact (all_infinite_subsets_reflection_iff E).mpr hglobal S hinf

theorem psWhole_inspecies : Inspecies PsEdge Whole :=
  (whole_inspecies_iff_cofinite_descendants PsEdge).mpr psNonDescendants_finite

theorem psReflection_iff_empty_or_infinite (S : NatSet) :
    Reflection PsEdge S ↔ (∀ v, ¬ S v) ∨ InfiniteSupport S :=
  reflection_iff_empty_or_infinite PsEdge
    (fun v => Or.inr (psNonDescendants_finite v)) psDescendants_infinite S

end SpeciesGlobalIAP

#print axioms SpeciesGlobalIAP.all_subsets_iap_iff
#print axioms SpeciesGlobalIAP.all_infinite_subsets_reflection_iff
#print axioms SpeciesGlobalIAP.all_subsets_iap_iff_all_infinite_subsets_reflection
#print axioms SpeciesGlobalIAP.whole_specieslike_iff
#print axioms SpeciesGlobalIAP.whole_inspecies_iff_cofinite_descendants
#print axioms SpeciesGlobalIAP.whole_iap_iff_inspecies_of_infinite_descendants
#print axioms SpeciesGlobalIAP.reflection_iff_empty_or_infinite
#print axioms SpeciesGlobalIAP.psWhole_inspecies
#print axioms SpeciesGlobalIAP.psReflection_iff_empty_or_infinite
