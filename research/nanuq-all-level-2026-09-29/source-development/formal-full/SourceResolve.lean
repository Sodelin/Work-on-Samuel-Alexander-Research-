import SourceQuartetRelation
import GraphQuartetExistence
import GraphSwitchingFinite
import GraphSwitchingCuts
import Mathlib.Data.Fintype.Powerset

namespace Nanuq.Source.RootedBinary

open Nanuq.Quartet

variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable {N : RootedBinary V E X}

private theorem two_of_four_classification : ∀ s : Finset (Fin 4), s.card = 2 →
    (0 ∈ s ∧ 1 ∈ s ∧ 2 ∉ s ∧ 3 ∉ s) ∨
    (2 ∈ s ∧ 3 ∈ s ∧ 0 ∉ s ∧ 1 ∉ s) ∨
    (0 ∈ s ∧ 2 ∈ s ∧ 1 ∉ s ∧ 3 ∉ s) ∨
    (1 ∈ s ∧ 3 ∈ s ∧ 0 ∉ s ∧ 2 ∉ s) ∨
    (0 ∈ s ∧ 3 ∈ s ∧ 1 ∉ s ∧ 2 ∉ s) ∨
    (1 ∈ s ∧ 2 ∈ s ∧ 0 ∉ s ∧ 3 ∉ s) := by
  decide +kernel

namespace Switching
variable (S : N.Switching)

/-- Existence of one of the three concrete edge-cut resolutions, obtained from
the proved 2+2 edge and a complete six-case classification of two of four. -/
theorem selected_resolution_exists (q : Fin 4 ↪ X) :
    ∃ r, S.graph.Resolves (fun i => N.leaf (q i)) r := by
  classical
  obtain ⟨e, _, ht⟩ := S.quartet_two_two_edge q
  let s := S.quartetSide q e (S.graph.target e)
  have he := S.graph.uniqueIncoming_all_bridges S.selected_uniqueIncoming S.selected_acyclic e
  have hT (i : Fin 4) (hi : i ∈ s) :
      S.graph.ReachWithout e (S.graph.target e) (N.leaf (q i)) :=
    (S.mem_quartetSide q e _ i).mp hi
  have hS (i : Fin 4) (hi : i ∉ s) :
      S.graph.ReachWithout e (S.graph.source e) (N.leaf (q i)) := by
    rcases S.graph.edge_side_cover e (S.selected_connected _ _) with h | h
    · exact h
    · exact False.elim (hi ((S.mem_quartetSide q e _ i).mpr h))
  rcases two_of_four_classification s ht with h | h | h | h | h | h
  · exact ⟨.xy_zw, e, he, Or.inr ⟨hS 2 h.2.2.1, hS 3 h.2.2.2,
      hT 0 h.1, hT 1 h.2.1⟩⟩
  · exact ⟨.xy_zw, e, he, Or.inl ⟨hS 0 h.2.2.1, hS 1 h.2.2.2,
      hT 2 h.1, hT 3 h.2.1⟩⟩
  · exact ⟨.xz_yw, e, he, Or.inr ⟨hS 1 h.2.2.1, hS 3 h.2.2.2,
      hT 0 h.1, hT 2 h.2.1⟩⟩
  · exact ⟨.xz_yw, e, he, Or.inl ⟨hS 0 h.2.2.1, hS 2 h.2.2.2,
      hT 1 h.1, hT 3 h.2.1⟩⟩
  · exact ⟨.xw_yz, e, he, Or.inr ⟨hS 1 h.2.2.1, hS 2 h.2.2.2,
      hT 0 h.1, hT 3 h.2.1⟩⟩
  · exact ⟨.xw_yz, e, he, Or.inl ⟨hS 0 h.2.2.1, hS 3 h.2.2.2,
      hT 1 h.1, hT 2 h.2.1⟩⟩

theorem selected_resolution_unique (q : Fin 4 ↪ X) :
    ∃! r, S.graph.Resolves (fun i => N.leaf (q i)) r := by
  obtain ⟨r, hr⟩ := S.selected_resolution_exists q
  exact ⟨r, hr, fun s hs => S.graph.resolution_unique hs hr⟩

/-- Actual raw switching resolution, with both existence and uniqueness proved. -/
noncomputable def resolve (q : Fin 4 ↪ X) : Resolution :=
  Classical.choose (S.selected_resolution_unique q)

theorem resolve_spec (q : Fin 4 ↪ X) :
    S.graph.Resolves (fun i => N.leaf (q i)) (S.resolve q) :=
  (Classical.choose_spec (S.selected_resolution_unique q)).1

theorem resolves_iff_eq_resolve (q : Fin 4 ↪ X) (r : Resolution) :
    S.graph.Resolves (fun i => N.leaf (q i)) r ↔ r = S.resolve q := by
  constructor
  · intro hr
    exact S.graph.resolution_unique hr (S.resolve_spec q)
  · rintro rfl
    exact S.resolve_spec q

theorem hasQuartet_of_original_bridge (hg : N.graph.GalledDetour) {a b c d : V}
    (h : N.graph.HasQuartet a b c d) : S.graph.HasQuartet a b c d := by
  obtain ⟨e, he, h⟩ := h
  let f : S.Edge := ⟨e, S.galled_bridge_retained hg he⟩
  have hf := S.graph.uniqueIncoming_all_bridges S.selected_uniqueIncoming S.selected_acyclic f
  refine ⟨f, hf, ?_⟩
  rcases h with h | h
  · exact Or.inl ⟨(S.selected_source_side_iff f he _).mpr h.1,
      (S.selected_source_side_iff f he _).mpr h.2.1,
      (S.selected_target_side_iff f he _).mpr h.2.2.1,
      (S.selected_target_side_iff f he _).mpr h.2.2.2⟩
  · exact Or.inr ⟨(S.selected_source_side_iff f he _).mpr h.1,
      (S.selected_source_side_iff f he _).mpr h.2.1,
      (S.selected_target_side_iff f he _).mpr h.2.2.1,
      (S.selected_target_side_iff f he _).mpr h.2.2.2⟩

theorem resolve_of_original_bridge (hg : N.graph.GalledDetour) (q : Fin 4 ↪ X)
    (r : Resolution) (h : N.graph.Resolves (fun i => N.leaf (q i)) r) :
    S.resolve q = r := by
  apply S.graph.resolution_unique (S.resolve_spec q)
  cases r <;> exact S.hasQuartet_of_original_bridge hg h

end Switching

/-- The distinct displayed quartet set, now using actual raw switching trees. -/
noncomputable def rawDisplayedQuartets (N : RootedBinary V E X) (q : Fin 4 ↪ X) :
    Finset Resolution := displayed (fun S : N.Switching => S.resolve q)

/-- The source averaging convention applied to proved actual raw resolutions.
The semidirected/up-down-path correspondence is a separate source convention bridge. -/
noncomputable def rawQuartetMean (N : RootedBinary V E X) (q : Fin 4 ↪ X) : ℚ :=
  sourceMean (fun S : N.Switching => S.resolve q)

theorem rawDisplayedQuartets_nonempty (N : RootedBinary V E X) (q : Fin 4 ↪ X) :
    (N.rawDisplayedQuartets q).Nonempty := displayed_nonempty _

/-- A source bridge separating the quartet 2+2 forces its actual resolution
in every switching and hence its exact distinct-quartet average. -/
theorem rawQuartetMean_of_bridge (N : RootedBinary V E X) (hg : N.graph.GalledDetour)
    (q : Fin 4 ↪ X) (r : Resolution)
    (h : N.graph.Resolves (fun i => N.leaf (q i)) r) :
    N.rawQuartetMean q = separatesFirstPair r := by
  have hc : (fun S : N.Switching => S.resolve q) = fun _ : N.Switching => r := by
    funext S
    exact S.resolve_of_original_bridge hg q r h
  unfold rawQuartetMean
  rw [hc, sourceMean_const]

end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.Switching.resolve_spec
#print axioms Nanuq.Source.RootedBinary.rawQuartetMean_of_bridge
