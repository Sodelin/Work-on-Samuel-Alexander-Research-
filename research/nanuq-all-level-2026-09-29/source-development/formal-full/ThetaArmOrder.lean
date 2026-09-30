import ThetaArmMetric

namespace Nanuq.Theta

instance (ka kb kc kd : Fin 4) (a b c d : Nat) : Decidable (hPairCut ka kb kc kd a b c d) := by
  unfold hPairCut tailPair centralPair
  infer_instance

/-- Four-point resolution expressed solely in arm membership and relative
position order. This form makes deletion/reindexing invariance explicit. -/
def orderQuartet {X : Type*} (tag : X → Fin 4) (pos : X → Nat) (a b c d : X) : Option Pairing :=
  if hPairCut (tag a) (tag b) (tag c) (tag d) (pos a) (pos b) (pos c) (pos d) then
    some .ab_cd
  else if hPairCut (tag a) (tag c) (tag b) (tag d) (pos a) (pos c) (pos b) (pos d) then
    some .ac_bd
  else if hPairCut (tag a) (tag d) (tag b) (tag c) (pos a) (pos d) (pos b) (pos c) then
    some .ad_bc
  else none

theorem tailPair_order_invariant {X : Type*} (tag : X → Fin 4) (old new : X → Nat)
    (horder : ∀ x y, tag x = tag y → (old x < old y ↔ new x < new y)) (a b c d : X) :
    tailPair (tag a) (tag b) (tag c) (tag d) (old a) (old b) (old c) (old d) ↔
      tailPair (tag a) (tag b) (tag c) (tag d) (new a) (new b) (new c) (new d) := by
  by_cases hab : tag a = tag b
  · have hother (x : X) :
        (tag x ≠ tag a ∨ (old x < old a ∧ old x < old b)) ↔
        (tag x ≠ tag a ∨ (new x < new a ∧ new x < new b)) := by
      by_cases hxa : tag x = tag a
      · simpa [hxa] using and_congr (horder x a hxa) (horder x b (hxa.trans hab))
      · simp [hxa]
    simpa [tailPair, hab] using and_congr (hother c) (hother d)
  · simp [tailPair, hab]

theorem hPairCut_order_invariant {X : Type*} (tag : X → Fin 4) (old new : X → Nat)
    (horder : ∀ x y, tag x = tag y → (old x < old y ↔ new x < new y)) (a b c d : X) :
    hPairCut (tag a) (tag b) (tag c) (tag d) (old a) (old b) (old c) (old d) ↔
      hPairCut (tag a) (tag b) (tag c) (tag d) (new a) (new b) (new c) (new d) := by
  exact or_congr (tailPair_order_invariant tag old new horder a b c d)
    (or_congr (tailPair_order_invariant tag old new horder c d a b) Iff.rfl)

theorem orderQuartet_invariant {X : Type*} (tag : X → Fin 4) (old new : X → Nat)
    (horder : ∀ x y, tag x = tag y → (old x < old y ↔ new x < new y)) (a b c d : X) :
    orderQuartet tag old a b c d = orderQuartet tag new a b c d := by
  simp only [orderQuartet, hPairCut_order_invariant tag old new horder a b c d,
    hPairCut_order_invariant tag old new horder a c b d,
    hPairCut_order_invariant tag old new horder a d b c]

#print axioms orderQuartet_invariant
end Nanuq.Theta
