import PairingCore
import PairingGARG
import WongAlexander

/-!
Exact maps into the repository's finite Wong gARG and real-dated Alexander
biosphere interfaces. A finite ARG is a truncation, not the infinite organism
population. No stochastic ARG law is instantiated by this file.
-/

namespace PairingBridge

open PairingCore PairingGARG SpeciesBridge

def code {T : Nat} (a : Node T) : Nat := copy a.1.val a.2

theorem code_injective (T : Nat) : Function.Injective (@code T) := by
  intro a b h
  have ht := congrArg (fun n => n/8) h
  have hl := congrArg lane h
  simp only [code, copy_gen, copy_lane] at ht hl
  exact Prod.ext (Fin.ext ht) hl

theorem finite_topology_iff_genome (T : Nat) (a b : Node T) :
    (finiteARG T).Topology a b ↔ Genome (code a) (code b) := by
  rw [topology_iff]
  simp only [Genome, code, copy_gen, copy_lane]
  exact and_congr_right (fun _ => eq_comm)

/-- All edges of the truncated organism pedigree, and only those edges, are
images of actual finite-gARG transmission edges under the supplied owner map. -/
theorem finite_pedigree_exact_image (T : Nat) (K : Schedule) (u v : Nat)
    (hu : u/4 ≤ T) (hv : v/4 ≤ T) :
    Edge K u v ↔ ∃ a b : Node T,
      (finiteARG T).Topology a b ∧ owner K (code a) = u ∧ owner K (code b) = v := by
  rw [edge_exact_image]
  constructor
  · rintro ⟨g, h, he, hg, hh⟩
    have gt := congrArg (fun n => n/4) hg
    have ht := congrArg (fun n => n/4) hh
    simp only [owner, org_gen] at gt ht
    let a : Node T := (⟨g/8, by omega⟩, lane g)
    let b : Node T := (⟨h/8, by omega⟩, lane h)
    have ha : code a = g := copy_decode g
    have hb : code b = h := copy_decode h
    refine ⟨a, b, ?_, by simpa only [ha] using hg, by simpa only [hb] using hh⟩
    apply (finite_topology_iff_genome T a b).mpr
    simpa only [ha, hb] using he
  · rintro ⟨a, b, he, ha, hb⟩
    exact ⟨code a, code b, (finite_topology_iff_genome T a b).mp he, ha, hb⟩

theorem extraction_retains_every_edge (T : Nat) (a b : Node T) :
    (finiteARG T).ExtractedAt 0 a b ↔ (finiteARG T).Topology a b := by
  constructor
  · intro h
    exact ((atLocus_iff T 0 a b).mp h.1).2
  · intro h
    exact ⟨(atLocus_iff T 0 a b).mpr ⟨rfl, h⟩, sampleAncestral_zero T b⟩

/-- Literal generation dates in the existing real-birthdate definition. -/
theorem generation_dated_biosphere (K : Schedule) : WongAlexander.RealDatedBiosphere (Edge K) := by
  refine ⟨fun u => ((u/4 : Nat) : ℝ), ?_, ?_, children_finite K, whole_infinite⟩
  · intro u v h
    have ht : u/4 < v/4 := by have := h.1; omega
    change ((u/4 : Nat) : ℝ) < ((v/4 : Nat) : ℝ)
    exact_mod_cast ht
  · intro r
    obtain ⟨n, hn⟩ := exists_nat_gt r
    refine ⟨List.range (4*n), ?_⟩
    intro u hu
    apply List.mem_range.mpr
    have hlt : ((u/4 : Nat) : ℝ) < n := lt_of_le_of_lt hu hn
    have hnat : u/4 < n := by exact_mod_cast hlt
    omega

end PairingBridge
