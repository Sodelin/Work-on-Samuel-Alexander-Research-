import Std

/-!
# Infinite labelled paths in finite phase graphs

A nonempty finite directed graph with an incoming edge of every label at
every vertex realizes every infinite word, with the initial phase allowed
to depend on the word. This is the standard finite-branching compactness
ingredient for the periodic-port application, not a priority claim.
The label type is arbitrary. The graph may have loops and need not have
an outgoing edge of every label at each vertex.
-/

namespace FinitePhasePaths

variable {A : Type} {p : Nat}

inductive Walk (E : Fin p → Fin p → A → Prop) (s : Nat → A) :
    Nat → Nat → Fin p → Fin p → Prop where
  | nil (k : Nat) (v : Fin p) : Walk E s k 0 v v
  | cons {k n : Nat} {u v w : Fin p} : E u v (s k) →
      Walk E s (k + 1) n v w → Walk E s k (n + 1) u w

theorem backward_word (E : Fin p → Fin p → A → Prop) (s : Nat → A)
    (incoming : ∀ v a, ∃ u, E u v a) (k n : Nat) (v : Fin p) :
    ∃ u, Walk E s k n u v := by
  induction n generalizing k v with
  | zero => exact ⟨v, .nil k v⟩
  | succ n ih =>
    obtain ⟨w, hw⟩ := ih (k + 1) v
    obtain ⟨u, hu⟩ := incoming w (s k)
    exact ⟨u, .cons hu hw⟩

private theorem finite_nat_bound (P : Nat → Nat → Prop) (n : Nat)
    (bounded : ∀ i, i < n → ∃ b, ∀ w, P i w → w < b) :
    ∃ b, ∀ i, i < n → ∀ w, P i w → w < b := by
  induction n with
  | zero => exact ⟨0, fun _ hi => False.elim (by omega)⟩
  | succ n ih =>
    obtain ⟨a, ha⟩ := ih (fun i hi => bounded i (by omega))
    obtain ⟨b, hb⟩ := bounded n (by omega)
    refine ⟨a + b, ?_⟩
    intro i hi w hw
    by_cases hin : i < n
    · have := ha i hin w hw; omega
    · have : i = n := by omega
      subst i
      have := hb w hw; omega

private theorem finite_bound (P : Fin p → Nat → Prop)
    (bounded : ∀ v, ∃ b, ∀ n, P v n → n < b) :
    ∃ b, ∀ v n, P v n → n < b := by
  let Q : Nat → Nat → Prop := fun i n => ∃ hi : i < p, P ⟨i, hi⟩ n
  obtain ⟨b, hb⟩ := finite_nat_bound Q p (by
    intro i hi
    obtain ⟨b, hb⟩ := bounded ⟨i, hi⟩
    refine ⟨b, ?_⟩
    intro n hn
    obtain ⟨hi', hn⟩ := hn
    exact hb n hn)
  refine ⟨b, ?_⟩
  intro v n hn
  exact hb v.val v.isLt n ⟨v.isLt, hn⟩

def Good (E : Fin p → Fin p → A → Prop) (s : Nat → A)
    (k : Nat) (v : Fin p) : Prop :=
  ¬ ∃ b, ∀ n, (∃ w, Walk E s k n v w) → n < b

theorem good_large {E : Fin p → Fin p → A → Prop} {s : Nat → A}
    {k : Nat} {v : Fin p} (good : Good E s k v) (b : Nat) :
    ∃ n w, b ≤ n ∧ Walk E s k n v w := by
  classical
  by_cases h : ∃ n w, b ≤ n ∧ Walk E s k n v w
  · exact h
  · apply False.elim
    apply good
    refine ⟨b, ?_⟩
    intro n hn
    obtain ⟨w, hw⟩ := hn
    by_cases hb : b ≤ n
    · exact False.elim (h ⟨n, w, hb, hw⟩)
    · omega

theorem good_start (hp : 0 < p) (E : Fin p → Fin p → A → Prop)
    (s : Nat → A) (incoming : ∀ v a, ∃ u, E u v a) :
    ∃ v, Good E s 0 v := by
  classical
  apply Classical.byContradiction
  intro hn
  have bounded : ∀ v, ∃ b, ∀ n, (∃ w, Walk E s 0 n v w) → n < b := by
    intro v
    apply Classical.byContradiction
    intro hb
    exact hn ⟨v, hb⟩
  obtain ⟨b, hb⟩ := finite_bound (fun v n => ∃ w, Walk E s 0 n v w) bounded
  obtain ⟨u, hu⟩ := backward_word E s incoming 0 b ⟨0, hp⟩
  have h := hb u b ⟨⟨0, hp⟩, hu⟩
  omega

theorem good_successor (E : Fin p → Fin p → A → Prop) (s : Nat → A)
    (k : Nat) (v : Fin p) (good : Good E s k v) :
    ∃ w, E v w (s k) ∧ Good E s (k + 1) w := by
  classical
  apply Classical.byContradiction
  intro hn
  have bounded : ∀ w, ∃ b, ∀ n,
      (E v w (s k) ∧ ∃ z, Walk E s (k + 1) n w z) → n < b := by
    intro w
    by_cases he : E v w (s k)
    · have hng : ¬ Good E s (k + 1) w := fun hg => hn ⟨w, he, hg⟩
      have hb : ∃ b, ∀ n, (∃ z, Walk E s (k + 1) n w z) → n < b :=
        Classical.byContradiction (fun h => hng h)
      obtain ⟨b, hb⟩ := hb
      exact ⟨b, fun n h => hb n h.2⟩
    · exact ⟨0, fun _ h => False.elim (he h.1)⟩
  obtain ⟨b, hb⟩ := finite_bound
    (fun w n => E v w (s k) ∧ ∃ z, Walk E s (k + 1) n w z) bounded
  obtain ⟨n, z, hnlarge, path⟩ := good_large good (b + 1)
  cases path with
  | nil => omega
  | @cons k m u w z he tail =>
    have hsmall := hb w m ⟨he, ⟨z, tail⟩⟩
    omega

theorem infinite_path_from_good (E : Fin p → Fin p → A → Prop)
    (s : Nat → A) (k : Nat) (v : Fin p) (good : Good E s k v) :
    ∃ path : Nat → Fin p, path 0 = v ∧
      ∀ n, E (path n) (path (n + 1)) (s (k + n)) := by
  classical
  let next : Nat → Fin p → Fin p := fun phase vertex =>
    if h : ∃ w, E vertex w (s phase) ∧ Good E s (phase + 1) w
    then Classical.choose h else vertex
  have next_spec : ∀ phase vertex, Good E s phase vertex →
      E vertex (next phase vertex) (s phase) ∧
      Good E s (phase + 1) (next phase vertex) := by
    intro phase vertex hg
    have h := good_successor E s phase vertex hg
    dsimp [next]
    rw [dif_pos h]
    exact Classical.choose_spec h
  let path : Nat → Fin p := fun n =>
    Nat.rec v (fun n vertex => next (k + n) vertex) n
  have hpath : ∀ n, Good E s (k + n) (path n) := by
    intro n
    induction n with
    | zero => exact good
    | succ n ih =>
      have h := (next_spec (k + n) (path n) ih).2
      simpa [path, Nat.add_assoc] using h
  refine ⟨path, rfl, ?_⟩
  intro n
  exact (next_spec (k + n) (path n) (hpath n)).1

/-- All states are possible starts; no single-start universality is claimed. -/
theorem realizes_all (hp : 0 < p) (E : Fin p → Fin p → A → Prop)
    (incoming : ∀ v a, ∃ u, E u v a) (s : Nat → A) :
    ∃ path : Nat → Fin p, ∀ n, E (path n) (path (n + 1)) (s n) := by
  obtain ⟨v, hv⟩ := good_start hp E s incoming
  obtain ⟨path, _, hp⟩ := infinite_path_from_good E s 0 v hv
  exact ⟨path, by simpa using hp⟩

#print axioms realizes_all

end FinitePhasePaths
