import Std

/-!
Two small verified parts of the proposed ordinal characterization.
The full finite-branching necessity and omega-rank calculation are proved in
ORDINAL-CHARACTERIZATION.md. This file verifies the compressed certificate's
soundness and the counterexample to ranking all phases.

The binary graph definition is copied exactly from BinaryAvoidance.lean at
bcef6da64672310b314f2bc17c96f9535fcaaf5b, with a separate namespace.
-/

namespace OrdinalCertificates

abbrev LabelledGraph (V A : Type) := V → V → A → Prop

def Prefix {V A : Type} (E : LabelledGraph V A) (s : Nat → A)
    (p : Nat → V) (len : Nat) : Prop :=
  ∀ k, k < len → E (p k) (p (k + 1)) (s k)

def Reachable {V A : Type} (E : LabelledGraph V A) (s : Nat → A)
    (v : V) (phase : Nat) : Prop :=
  ∃ p : Nat → V, p phase = v ∧ Prefix E s p phase

def Matches {V A : Type} (E : LabelledGraph V A) (s : Nat → A)
    (p : Nat → V) : Prop :=
  ∀ k, E (p k) (p (k + 1)) (s k)

/-- Values at unreachable pairs are immaterial. -/
def NaturalCertificate {V A : Type} (E : LabelledGraph V A) (s : Nat → A)
    (r : V → Nat → Nat) : Prop :=
  ∀ v k, Reachable E s v k → ∀ w, E v w (s k) →
    r w (k + 1) < r v k

theorem certificate_bounds_every_prefix {V A : Type}
    (E : LabelledGraph V A) (s : Nat → A) (r : V → Nat → Nat)
    (hr : NaturalCertificate E s r) (p : Nat → V) (len : Nat)
    (hp : Prefix E s p len) : r (p len) len + len ≤ r (p 0) 0 := by
  induction len with
  | zero => omega
  | succ n ih =>
    have hpre : Prefix E s p n := fun k hk => hp k (by omega)
    have old := ih hpre
    have reachable : Reachable E s (p n) n := ⟨p, rfl, hpre⟩
    have next := hr (p n) n reachable (p (n + 1)) (hp n (by omega))
    omega

theorem certificate_excludes_realization {V A : Type}
    (E : LabelledGraph V A) (s : Nat → A) (r : V → Nat → Nat)
    (hr : NaturalCertificate E s r) : ¬ ∃ p, Matches E s p := by
  rintro ⟨p, hp⟩
  let len := r (p 0) 0 + 1
  have hpre : Prefix E s p len := fun k _ => hp k
  have bound := certificate_bounds_every_prefix E s r hr p len hpre
  dsimp [len] at bound
  omega

def row (s : Nat → Bool) (w : Nat) : Bool :=
  if w % 2 = 0 then s (w / 2) else !(s (w / 2))

def Edge (s : Nat → Bool) (u w : Nat) (label : Bool) : Prop :=
  2 ≤ w ∧ ((w = u + 1 ∧ label = row s w) ∨
    (w = u + 2 ∧ label = !(row s w)))

theorem row_odd (s : Nat → Bool) (n : Nat) :
    row s (2 * n + 1) = !(s n) := by
  have hm : (2 * n + 1) % 2 = 1 := by omega
  have hd : (2 * n + 1) / 2 = n := by omega
  simp [row, hm, hd]

/-- Every P_s realizes the tail s[1:] along 1,3,5,... . -/
theorem odd_ray_realizes_tail (s : Nat → Bool) (k : Nat) :
    Edge s (2 * k + 1) (2 * (k + 1) + 1) (s (k + 1)) := by
  refine ⟨by omega, Or.inr ⟨by omega, ?_⟩⟩
  rw [row_odd]
  simp

/-- An all-phase natural certificate fails for every P_s, including avoiders. -/
theorem no_all_phase_natural_rank (s : Nat → Bool) :
    ¬ ∃ r : Nat → Nat → Nat,
      ∀ v k w, Edge s v w (s k) → r w (k + 1) < r v k := by
  rintro ⟨r, hr⟩
  have bound : ∀ k, r (2 * k + 1) (k + 1) + k ≤ r 1 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have next := hr (2 * k + 1) (k + 1) (2 * (k + 1) + 1)
        (odd_ray_realizes_tail s k)
      omega
  have impossible := bound (r 1 1 + 1)
  omega

end OrdinalCertificates

#print axioms OrdinalCertificates.certificate_bounds_every_prefix
#print axioms OrdinalCertificates.certificate_excludes_realization
#print axioms OrdinalCertificates.odd_ray_realizes_tail
#print axioms OrdinalCertificates.no_all_phase_natural_rank
