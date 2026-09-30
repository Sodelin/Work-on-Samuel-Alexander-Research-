import SourceResolve

/-! Pair symmetries of the actual raw graph's distinct-topology mean. -/
namespace Nanuq.Quartet

def Resolution.swapCross : Resolution → Resolution
  | .xy_zw => .xy_zw
  | .xz_yw => .xw_yz
  | .xw_yz => .xz_yw

instance : Fintype Resolution := ⟨{.xy_zw, .xz_yw, .xw_yz}, by intro r; cases r <;> simp⟩

set_option maxRecDepth 32768 in
theorem distinctMean_swapCross : ∀ s : Finset Resolution,
    distinctMean (s.image Resolution.swapCross) = distinctMean s := by
  decide +kernel

theorem sourceMean_swapCross {S : Type*} [Fintype S] (resolve : S → Resolution) :
    sourceMean (fun s => (resolve s).swapCross) = sourceMean resolve := by
  simpa [sourceMean, displayed, Finset.image_image, Function.comp_def] using
    distinctMean_swapCross (displayed resolve)

def swapFirst {X : Type*} (q : Fin 4 ↪ X) : Fin 4 ↪ X :=
  (Equiv.swap (0 : Fin 4) 1).toEmbedding.trans q

def swapLast {X : Type*} (q : Fin 4 ↪ X) : Fin 4 ↪ X :=
  (Equiv.swap (2 : Fin 4) 3).toEmbedding.trans q

end Nanuq.Quartet

namespace Nanuq.Source.EdgeGraph

open Nanuq.Quartet
variable {V E : Type*} (G : EdgeGraph V E)

theorem hasQuartet_swap_left {a b c d : V} (h : G.HasQuartet a b c d) :
    G.HasQuartet b a c d := by
  obtain ⟨e, he, h | h⟩ := h
  · exact ⟨e, he, Or.inl ⟨h.2.1, h.1, h.2.2.1, h.2.2.2⟩⟩
  · exact ⟨e, he, Or.inr ⟨h.1, h.2.1, h.2.2.2, h.2.2.1⟩⟩

theorem hasQuartet_swap_pairs {a b c d : V} (h : G.HasQuartet a b c d) :
    G.HasQuartet c d a b := by
  obtain ⟨e, he, h⟩ := h
  exact ⟨e, he, h.symm⟩

theorem resolves_swap_first {v : Fin 4 → V} {r : Resolution} (h : G.Resolves v r) :
    G.Resolves (fun i => v (Equiv.swap (0 : Fin 4) 1 i)) r.swapCross := by
  cases r
  · simpa [Resolves, Resolution.swapCross, Equiv.swap_apply_def] using G.hasQuartet_swap_left h
  · simpa [Resolves, Resolution.swapCross, Equiv.swap_apply_def] using G.hasQuartet_swap_pairs h
  · simpa [Resolves, Resolution.swapCross, Equiv.swap_apply_def] using G.hasQuartet_swap_pairs h

theorem resolves_swap_last {v : Fin 4 → V} {r : Resolution} (h : G.Resolves v r) :
    G.Resolves (fun i => v (Equiv.swap (2 : Fin 4) 3 i)) r.swapCross := by
  cases r
  · simpa [Resolves, Resolution.swapCross, Equiv.swap_apply_def] using G.hasQuartet_swap_right h
  · simpa [Resolves, Resolution.swapCross, Equiv.swap_apply_def] using h
  · simpa [Resolves, Resolution.swapCross, Equiv.swap_apply_def] using h

end Nanuq.Source.EdgeGraph

namespace Nanuq.Source.RootedBinary

open Nanuq.Quartet
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable {N : RootedBinary V E X}

namespace Switching

theorem resolve_swap_first (S : N.Switching) (q : Fin 4 ↪ X) :
    S.resolve (swapFirst q) = (S.resolve q).swapCross := by
  apply S.graph.resolution_unique (S.resolve_spec (swapFirst q))
  exact S.graph.resolves_swap_first (S.resolve_spec q)

theorem resolve_swap_last (S : N.Switching) (q : Fin 4 ↪ X) :
    S.resolve (swapLast q) = (S.resolve q).swapCross := by
  apply S.graph.resolution_unique (S.resolve_spec (swapLast q))
  exact S.graph.resolves_swap_last (S.resolve_spec q)

end Switching

theorem rawQuartetMean_swap_first (N : RootedBinary V E X) (q : Fin 4 ↪ X) :
    N.rawQuartetMean (swapFirst q) = N.rawQuartetMean q := by
  unfold rawQuartetMean
  simp_rw [Switching.resolve_swap_first]
  exact sourceMean_swapCross _

theorem rawQuartetMean_swap_last (N : RootedBinary V E X) (q : Fin 4 ↪ X) :
    N.rawQuartetMean (swapLast q) = N.rawQuartetMean q := by
  unfold rawQuartetMean
  simp_rw [Switching.resolve_swap_last]
  exact sourceMean_swapCross _

#print axioms rawQuartetMean_swap_first
#print axioms rawQuartetMean_swap_last

end Nanuq.Source.RootedBinary
