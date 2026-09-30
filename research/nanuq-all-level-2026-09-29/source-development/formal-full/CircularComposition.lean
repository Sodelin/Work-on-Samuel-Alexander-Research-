import CircularMixture
import CircularDecomposition
import AnchorComposition

/-! Circular decomposition is preserved by finite sums and port projections
whose interval preimages are circular intervals. The interval property is an
explicit remaining graph/embedding obligation, not a substitute definition of
source outer-labeled planarity. -/
namespace Nanuq.Reconstruction

open scoped BigOperators
open Nanuq.Weighted Nanuq.Composition
variable {n m : Nat}

theorem circular_decomposable_coefficient_nonneg (d : Matrix n)
    (hd : CircularDecomposable d) (i j : Fin n) (hij : i < j) :
    0 ≤ circularAlpha d i j := by
  obtain ⟨w, hw, heq⟩ := hd
  have he : d = splitMixture w := by funext x y; exact heq x y
  rw [he, alpha_splitMixture w i j hij]
  exact mul_nonneg (by decide) (hw i j hij)

/-- Explicit geometric content required of a taxon-to-port map. -/
def CircularPortMap (project : Fin n → Fin m) : Prop :=
  ∀ i j, i < j → ∃ a b : Fin n, a < b ∧
    ((∀ x, inArc i j (project x) ↔ inArc a b x) ∨
     (∀ x, inArc i j (project x) ↔ ¬ inArc a b x))

theorem circular_port_gap_pullback (project : Fin n → Fin m)
    (hmap : CircularPortMap project) (i j : Fin m) (hij : i < j) :
    ∃ a b : Fin n, a < b ∧
      (fun x y => gapSplit i j (project x) (project y)) = gapSplit a b := by
  obtain ⟨a,b,hab,h | h⟩ := hmap i j hij
  · refine ⟨a,b,hab,?_⟩
    funext x y
    exact gapSplit_pullback project i j a b hij hab h x y
  · refine ⟨a,b,hab,?_⟩
    funext x y
    rw [gapSplit_eq_separation _ _ _ _ hij, gapSplit_eq_separation _ _ _ _ hab]
    simp only [h, not_iff_not]

theorem circular_decomposable_port_pullback (d : Matrix m)
    (hd : CircularDecomposable d) (project : Fin n → Fin m)
    (hmap : CircularPortMap project) :
    CircularDecomposable (fun x y => d (project x) (project y)) := by
  have hlaws := circular_decomposable_pseudometric d hd
  obtain ⟨w, hw, heq⟩ := hd
  apply circular_decomposable_of_coefficients
  · intro x y; exact hlaws.2.2.1 _ _
  · intro x; exact hlaws.2.1 _
  · intro i j hij
    have hexpand : circularAlpha (fun x y => d (project x) (project y)) i j =
        ∑ pq ∈ upperPairs m, w pq.1 pq.2 *
          circularAlpha (fun x y => gapSplit pq.1 pq.2 (project x) (project y)) i j := by
      simp only [circularAlpha, heq, mul_add, mul_sub,
        Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hexpand]
    apply Finset.sum_nonneg
    intro pq hpq
    have hord := (mem_upperPairs _ _).mp hpq
    obtain ⟨a,b,hab,he⟩ := circular_port_gap_pullback project hmap pq.1 pq.2 hord
    rw [he, alpha_gapSplit _ _ _ _ hab hij]
    exact mul_nonneg (hw _ _ hord) (by split_ifs <;> norm_num)

theorem circular_decomposable_sum {B : Type*} [Fintype B] (d : B → Matrix n)
    (hd : ∀ b, CircularDecomposable (d b)) :
    CircularDecomposable (fun x y => ∑ b, d b x y) := by
  apply circular_decomposable_of_coefficients
  · intro x y
    apply Finset.sum_congr rfl
    intro b _
    exact (circular_decomposable_pseudometric _ (hd b)).2.2.1 x y
  · intro x
    simp only [(fun b => (circular_decomposable_pseudometric _ (hd b)).2.1 x)]
    exact Finset.sum_const_zero
  · intro i j hij
    have he : circularAlpha (fun x y => ∑ b, d b x y) i j =
        ∑ b, circularAlpha (d b) i j := by
      simp only [circularAlpha, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [he]
    exact Finset.sum_nonneg (fun b _ => circular_decomposable_coefficient_nonneg _ (hd b) i j hij)

theorem source_circular_of_anchor_composition {B : Type*} [Fintype B]
    (k : B → Nat) (rho : QuartetData n) (localRho : ∀ b, QuartetData (k b))
    (hsym : WitnessSymmetric rho) (hlocalSym : ∀ b, WitnessSymmetric (localRho b))
    (project : ∀ b, Fin n → Fin (k b))
    (hanchor : ∀ p q x y, orderedAnchor rho p q x y =
      ∑ b, orderedAnchor (localRho b) (project b p) (project b q) (project b x) (project b y))
    (hlocals : ∀ b, CircularDecomposable (weightedNanuq (localRho b) (portMass (project b))))
    (hports : ∀ b, CircularPortMap (project b)) :
    CircularDecomposable (sourceNanuq rho) := by
  have he : sourceNanuq rho = fun x y => ∑ b,
      weightedNanuq (localRho b) (portMass (project b)) (project b x) (project b y) := by
    funext x y
    exact source_composition_of_anchor_identity k rho localRho hsym hlocalSym project hanchor x y
  rw [he]
  exact circular_decomposable_sum _ (fun b =>
    circular_decomposable_port_pullback _ (hlocals b) (project b) (hports b))

#print axioms circular_decomposable_port_pullback
#print axioms source_circular_of_anchor_composition

end Nanuq.Reconstruction
