import AnchorPortPatterns

/-! Unique medians of the four triples force one four-port center or two
three-port centers, with all other projections using at most two ports. -/
namespace Nanuq.PortPatterns
open scoped BigOperators

variable {B : Type*} [Fintype B] [DecidableEq B]
variable {P : B → Type*} [∀ b, DecidableEq (P b)]

/-- Pure finite counting; the graph lane supplies actual unique triple medians. -/
theorem sum_tripleCount_of_unique (f : ∀ b, Fin 4 → P b)
    (hunique : ∀ i : Fin 4, ∃! b, tripleInjective (f b) i) :
    ∑ b, tripleCount (f b) = 4 := by
  have hone (i : Fin 4) : (∑ b, if tripleInjective (f b) i then 1 else 0) = (1 : Nat) := by
    obtain ⟨b,hb,hu⟩ := hunique i
    have he (c : B) : tripleInjective (f c) i ↔ c = b := by
      constructor
      · exact hu c
      · intro hc; subst c; exact hb
    simp_rw [he]
    simp
  simp only [tripleCount]
  rw [Finset.sum_comm]
  simp_rw [hone]
  simp


theorem tripleCount_indicator {Q : Type*} [DecidableEq Q] (f : Fin 4 → Q) :
    tripleCount f = (if portCount f = 4 then 4 else 0) + (if portCount f = 3 then 2 else 0) := by
  rw [tripleCount_by_portCount]
  split_ifs <;> omega

theorem sum_tripleCount_eq_port_counts (f : ∀ b, Fin 4 → P b) :
    (∑ b, tripleCount (f b)) =
      4 * (Finset.univ.filter (fun b => portCount (f b) = 4)).card +
      2 * (Finset.univ.filter (fun b => portCount (f b) = 3)).card := by
  simp_rw [tripleCount_indicator]
  rw [Finset.sum_add_distrib]
  simp [← Finset.sum_filter,Nat.mul_comm]

/-- The full local branching alternatives follow from the four unique triple
medians, without assuming the number of active blobs in advance. -/
theorem branching_port_counts_of_unique (f : ∀ b, Fin 4 → P b)
    (hunique : ∀ i : Fin 4, ∃! b, tripleInjective (f b) i) :
    ((Finset.univ.filter (fun b => portCount (f b) = 4)).card = 1 ∧
      (Finset.univ.filter (fun b => portCount (f b) = 3)).card = 0) ∨
    ((Finset.univ.filter (fun b => portCount (f b) = 4)).card = 0 ∧
      (Finset.univ.filter (fun b => portCount (f b) = 3)).card = 2) := by
  have hsum := sum_tripleCount_of_unique f hunique
  rw [sum_tripleCount_eq_port_counts] at hsum
  omega

#print axioms sum_tripleCount_of_unique
#print axioms branching_port_counts_of_unique
end Nanuq.PortPatterns
