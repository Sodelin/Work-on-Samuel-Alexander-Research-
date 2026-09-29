import Mathlib.Order.WellFounded
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.EquivFin

/-!
# Natural avoidance certificates without vertex or alphabet encoding

For arbitrary vertex and label types, an actual infinite labelled path exists
iff the reachable vertex/phase transition relation has an infinite chain.
With finitely many possible children per vertex and fixed label, avoidance
is equivalent to a strictly decreasing natural-valued certificate. The
constructed certificate is pointwise least and its values are attained
finite-chain lengths. No birth ordering, root assumptions, decidable graph,
finite alphabet, or computability premise is needed.

This is a standard consequence of well-founded recursion with finite maxima,
formalized here to remove the prior Bool/Nat model restriction. It does not
claim a new general mathematical method or biological identification result.
-/

namespace GenericCertificate

universe u v
variable {α : Type u}

noncomputable def finiteHeight (R : α → α → Prop)
    (fin : ∀ x, Finite {y // R y x}) (wf : WellFounded R) : α → Nat :=
  wf.fix fun x rec => by
    letI := fin x
    letI := Fintype.ofFinite {y // R y x}
    exact Finset.univ.sup (fun y : {y // R y x} => rec y.1 y.2 + 1)

theorem finiteHeight_eq (R : α → α → Prop)
    (fin : ∀ x, Finite {y // R y x}) (wf : WellFounded R) (x : α) :
    finiteHeight R fin wf x = by
      letI := fin x
      letI := Fintype.ofFinite {y // R y x}
      exact Finset.univ.sup (fun y : {y // R y x} => finiteHeight R fin wf y.1 + 1) := by
  unfold finiteHeight
  rw [WellFounded.fix_eq]

theorem finiteHeight_decreases (R : α → α → Prop)
    (fin : ∀ x, Finite {y // R y x}) (wf : WellFounded R)
    {x y : α} (hy : R y x) : finiteHeight R fin wf y < finiteHeight R fin wf x := by
  let := fin x
  let := Fintype.ofFinite {y // R y x}
  rw [finiteHeight_eq R fin wf x]
  exact Nat.lt_of_succ_le (Finset.le_sup (f := fun z : {y // R y x} =>
    finiteHeight R fin wf z.1 + 1) (Finset.mem_univ ⟨y, hy⟩))



/-- Exact length of a finite descending chain, including the length-zero chain. -/
inductive ChainLength (R : α → α → Prop) : α → Nat → Prop where
  | zero (x) : ChainLength R x 0
  | cons {x y n} : R y x → ChainLength R y n → ChainLength R x (n+1)

theorem finiteHeight_least (R : α → α → Prop)
    (fin : ∀ x, Finite {y // R y x}) (wf : WellFounded R)
    (rank : α → Nat) (cert : ∀ {x y}, R y x → rank y < rank x) :
    ∀ x, finiteHeight R fin wf x ≤ rank x := by
  intro x
  induction x using wf.induction with
  | h x ih =>
    let := fin x
    let := Fintype.ofFinite {y // R y x}
    rw [finiteHeight_eq]
    apply Finset.sup_le
    intro y _
    have small := ih y.1 y.2
    have strict := cert y.2
    omega

theorem chainLength_le_height (R : α → α → Prop)
    (fin : ∀ x, Finite {y // R y x}) (wf : WellFounded R)
    {x : α} {n : Nat} (chain : ChainLength R x n) : n ≤ finiteHeight R fin wf x := by
  induction chain with
  | zero => omega
  | cons hy _ ih =>
    have strict := finiteHeight_decreases R fin wf hy
    omega

theorem finiteHeight_attained (R : α → α → Prop)
    (fin : ∀ x, Finite {y // R y x}) (wf : WellFounded R) :
    ∀ x, ChainLength R x (finiteHeight R fin wf x) := by
  intro x
  induction x using wf.induction with
  | h x ih =>
    let := fin x
    let := Fintype.ofFinite {y // R y x}
    by_cases hex : ∃ y, R y x
    · obtain ⟨y,hy⟩ := hex
      obtain ⟨z, _, hmax⟩ := Finset.exists_mem_eq_sup
        (Finset.univ : Finset {y // R y x}) ⟨⟨y,hy⟩, Finset.mem_univ _⟩
        (fun z : {y // R y x} => finiteHeight R fin wf z.1 + 1)
      rw [finiteHeight_eq, hmax]
      exact ChainLength.cons z.2 (ih z.1 z.2)
    · have hzero : finiteHeight R fin wf x = 0 := by
        rw [finiteHeight_eq]
        apply Nat.eq_zero_of_le_zero
        apply Finset.sup_le
        intro y _
        exact False.elim (hex ⟨y.1, y.2⟩)
      rw [hzero]
      exact ChainLength.zero x

variable {V : Type u} {Label : Type v}

abbrev Graph (V : Type u) (Label : Type v) := V → V → Label → Prop

def Realizes (E : Graph V Label) (s : Nat → Label) : Prop :=
  ∃ p : Nat → V, ∀ n, E (p n) (p (n+1)) (s n)

def Reachable (E : Graph V Label) (s : Nat → Label) (vertex : V) (phase : Nat) : Prop :=
  ∃ p : Nat → V, p phase = vertex ∧ ∀ n, n < phase → E (p n) (p (n+1)) (s n)

abbrev State (E : Graph V Label) (s : Nat → Label) :=
  {q : V × Nat // Reachable E s q.1 q.2}

/-- The child is the first argument, so well-foundedness ranks forward transitions downwards. -/
def Step (E : Graph V Label) (s : Nat → Label) (child parent : State E s) : Prop :=
  child.1.2 = parent.1.2 + 1 ∧ E parent.1.1 child.1.1 (s parent.1.2)

theorem realizes_iff_state_chain (E : Graph V Label) (s : Nat → Label) :
    Realizes E s ↔ ∃ f : Nat → State E s, ∀ n, Step E s (f (n+1)) (f n) := by
  constructor
  · rintro ⟨p, hp⟩
    let f : Nat → State E s := fun n => ⟨(p n,n), p, rfl, fun j _ => hp j⟩
    exact ⟨f, fun n => ⟨rfl, hp n⟩⟩
  · rintro ⟨f, hf⟩
    let k := (f 0).1.2
    obtain ⟨p, hp0, hp⟩ := (f 0).2
    have phase : ∀ n, (f n).1.2 = k + n := by
      intro n
      induction n with
      | zero => simp [k]
      | succ n ih =>
        have h := (hf n).1
        omega
    let q : Nat → V := fun n => if n < k then p n else (f (n-k)).1.1
    refine ⟨q, fun n => ?_⟩
    by_cases hn : n < k
    · by_cases hn1 : n+1 < k
      · simpa [q, hn, hn1] using hp n hn
      · have heq : n+1 = k := by omega
        have hzero : n+1-k=0 := by omega
        have h := hp n hn
        rw [heq] at h
        change p k = (f 0).1.1 at hp0
        rw [hp0] at h
        simpa [q, hn, hn1, hzero] using h
    · have hn1 : ¬ n+1<k := by omega
      have heq : n+1-k=(n-k)+1 := by omega
      have hk : (f (n-k)).1.2 = n := by
        rw [phase]
        omega
      have h := (hf (n-k)).2
      rw [hk] at h
      simpa [q, hn, hn1, heq] using h

theorem avoids_iff_wellFounded (E : Graph V Label) (s : Nat → Label) :
    (¬ Realizes E s) ↔ WellFounded (Step E s) := by
  rw [realizes_iff_state_chain, wellFounded_iff_isEmpty_descending_chain]
  constructor
  · intro h
    exact ⟨fun ⟨f, hf⟩ => h ⟨f, hf⟩⟩
  · intro h ⟨f, hf⟩
    exact h.false ⟨f, hf⟩

/-- Finiteness for each fixed label suffices; finiteness across all labels is stronger. -/
def FiniteLabelChildren (E : Graph V Label) : Prop :=
  ∀ v label, Set.Finite {w | E v w label}

theorem finiteLabelChildren_of_finite_children (E : Graph V Label)
    (fin : ∀ v, Set.Finite {w | ∃ label, E v w label}) : FiniteLabelChildren E := by
  intro v label
  let : Finite {w // ∃ a, E v w a} := (fin v).to_subtype
  let f : {w // E v w label} → {w // ∃ a, E v w a} := fun w => ⟨w.1, label, w.2⟩
  apply Finite.of_injective f
  intro a b h
  apply Subtype.ext
  exact congrArg (fun z : {w // ∃ a, E v w a} => z.1) h

theorem finite_state_children (E : Graph V Label) (s : Nat → Label)
    (fin : FiniteLabelChildren E) (x : State E s) :
    Finite {y : State E s // Step E s y x} := by
  let : Finite {w // E x.1.1 w (s x.1.2)} := (fin x.1.1 (s x.1.2)).to_subtype
  let f : {y : State E s // Step E s y x} → {w // E x.1.1 w (s x.1.2)} :=
    fun y => ⟨y.1.1.1, y.2.2⟩
  apply Finite.of_injective f
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg Subtype.val hab
  · exact a.2.1.trans b.2.1.symm

def NaturalCertificate (E : Graph V Label) (s : Nat → Label)
    (rank : State E s → Nat) : Prop :=
  ∀ {child parent}, Step E s child parent → rank child < rank parent

theorem certificate_excludes_realization (E : Graph V Label) (s : Nat → Label)
    (rank : State E s → Nat) (cert : NaturalCertificate E s rank) : ¬ Realizes E s := by
  rintro h
  obtain ⟨f,hf⟩ := (realizes_iff_state_chain E s).mp h
  have bounded : ∀ n, rank (f n)+n ≤ rank (f 0) := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
      have hdec := cert (hf n)
      omega
  have := bounded (rank (f 0)+1)
  omega

theorem avoids_iff_natural_certificate (E : Graph V Label) (s : Nat → Label)
    (fin : FiniteLabelChildren E) :
    (¬ Realizes E s) ↔ ∃ rank, NaturalCertificate E s rank := by
  constructor
  · intro avoid
    have wf := (avoids_iff_wellFounded E s).mp avoid
    exact ⟨finiteHeight (Step E s) (finite_state_children E s fin) wf,
      fun {_ _} h => finiteHeight_decreases _ _ _ h⟩
  · rintro ⟨rank, cert⟩
    exact certificate_excludes_realization E s rank cert

/-- A least certificate exists and every value is an attained finite continuation length. -/
theorem avoids_has_least_attained_certificate (E : Graph V Label) (s : Nat → Label)
    (fin : FiniteLabelChildren E) (avoid : ¬ Realizes E s) :
    ∃ rank, NaturalCertificate E s rank ∧
      (∀ other, NaturalCertificate E s other → ∀ x, rank x ≤ other x) ∧
      (∀ x, ChainLength (Step E s) x (rank x)) ∧
      (∀ x n, ChainLength (Step E s) x n → n ≤ rank x) := by
  have wf := (avoids_iff_wellFounded E s).mp avoid
  let fin' := finite_state_children E s fin
  refine ⟨finiteHeight (Step E s) fin' wf, ?_, ?_, ?_, ?_⟩
  · exact fun {_ _} h => finiteHeight_decreases _ _ _ h
  · intro other cert
    exact finiteHeight_least _ _ _ other cert
  · exact finiteHeight_attained _ _ _
  · intro x n chain
    exact chainLength_le_height _ _ _ chain

#print axioms GenericCertificate.realizes_iff_state_chain
#print axioms GenericCertificate.avoids_iff_wellFounded
#print axioms GenericCertificate.finiteHeight_decreases
#print axioms GenericCertificate.finiteLabelChildren_of_finite_children
#print axioms GenericCertificate.avoids_iff_natural_certificate
#print axioms GenericCertificate.finiteHeight_least
#print axioms GenericCertificate.finiteHeight_attained
#print axioms GenericCertificate.avoids_has_least_attained_certificate

end GenericCertificate
