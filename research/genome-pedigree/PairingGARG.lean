import WongGARG
import Mathlib.Data.Fintype.Prod

/-!
# The eight-lane finite prefix in the existing genome-ARG interface

The nodes are genome copies in generations `0, ..., T`, with eight lanes at
each generation. Every record is a one-generation transmission along one
lane, carrying the interval `[0,1)`. The eight last-generation copies are
sampled. This is a deterministic finite representation; it does not assert
an equality of stochastic observation laws or make the infinite lane graph
an instance of the finite `WongGARG.GARG` structure.
-/

set_option autoImplicit false

namespace PairingGARG

open WongGARG AncestryViews

noncomputable section

abbrev Node (T : Nat) := Fin (T + 1) × Fin 8

def fullInterval : WongGARG.Interval Nat :=
  ⟨0, 1, by decide⟩

def record (T : Nat) (e : Fin T × Fin 8) :
    WongGARG.EdgeRecord (Node T) Nat where
  parent := (e.1.castSucc, e.2)
  child := (e.1.succ, e.2)
  regions := {fullInterval}
  disjoint := by
    intro I hI J hJ different
    have hI' : I = fullInterval := Finset.mem_singleton.mp hI
    have hJ' : J = fullInterval := Finset.mem_singleton.mp hJ
    exact False.elim (different (hI'.trans hJ'.symm))

def records (T : Nat) : Finset (WongGARG.EdgeRecord (Node T) Nat) := by
  classical
  exact Finset.univ.image (record T)

theorem mem_records_iff (T : Nat) (e : WongGARG.EdgeRecord (Node T) Nat) :
    e ∈ records T ↔ ∃ k : Fin T × Fin 8, record T k = e := by
  classical
  simp [records]

theorem record_topology_iff (T : Nat) (a b : Node T) :
    WongGARG.RecordTopology (records T) a b ↔
      b.1.val = a.1.val + 1 ∧ b.2 = a.2 := by
  constructor
  · rintro ⟨e, member, ha, hb⟩
    obtain ⟨k, rfl⟩ := (mem_records_iff T e).mp member
    have hta := congrArg (fun z : Node T => z.1.val) ha
    have htb := congrArg (fun z : Node T => z.1.val) hb
    have hla := congrArg (fun z : Node T => z.2) ha
    have hlb := congrArg (fun z : Node T => z.2) hb
    constructor
    · change k.1.val = a.1.val at hta
      change k.1.val + 1 = b.1.val at htb
      omega
    · exact hlb.symm.trans hla
  · rintro ⟨time, lane⟩
    have before : a.1.val < T := by
      have bound := b.1.isLt
      omega
    let k : Fin T × Fin 8 := (⟨a.1.val, before⟩, a.2)
    refine ⟨record T k, (mem_records_iff T _).mpr ⟨k, rfl⟩, ?_, ?_⟩
    · apply Prod.ext
      · apply Fin.ext
        rfl
      · rfl
    · apply Prod.ext
      · apply Fin.ext
        exact time.symm
      · exact lane.symm

theorem record_reach_strict {T : Nat} {a b : Node T}
    (path : Reach (WongGARG.RecordTopology (records T)) a b) :
    a.1.val < b.1.val := by
  induction path with
  | edge h =>
      have time := ((record_topology_iff T _ _).mp h).1
      omega
  | snoc _ h ih =>
      have time := ((record_topology_iff T _ _).mp h).1
      omega

/-- A literal finite gARG, with all last-generation copies sampled. -/
def finiteARG (T : Nat) : WongGARG.GARG (Fin (T + 1) × Fin 8) Nat where
  samples := Finset.univ.filter (fun a => a.1.val = T)
  records := records T
  acyclic := by
    intro a path
    exact Nat.lt_irrefl a.1.val (record_reach_strict path)

theorem topology_iff (T : Nat) (a b : Node T) :
    (finiteARG T).Topology a b ↔ b.1.val = a.1.val + 1 ∧ b.2 = a.2 :=
  record_topology_iff T a b

theorem sample_iff (T : Nat) (a : Node T) :
    a ∈ (finiteARG T).samples ↔ a.1.val = T := by
  simp [finiteARG]

theorem nonemptyAnnotations (T : Nat) : (finiteARG T).NonemptyAnnotations := by
  intro e member
  obtain ⟨k, rfl⟩ := (mem_records_iff T e).mp member
  exact ⟨fullInterval, Finset.mem_singleton_self fullInterval⟩

theorem atLocus_iff (T x : Nat) (a b : Node T) :
    (finiteARG T).AtLocus x a b ↔ x = 0 ∧ (finiteARG T).Topology a b := by
  constructor
  · rintro ⟨e, member, ha, hb, covered⟩
    obtain ⟨k, rfl⟩ := (mem_records_iff T e).mp member
    obtain ⟨I, hI, position⟩ := covered
    have hI' : I = fullInterval := Finset.mem_singleton.mp hI
    subst I
    change 0 ≤ x ∧ x < 1 at position
    exact ⟨by omega, record T k, member, ha, hb⟩
  · rintro ⟨rfl, e, member, ha, hb⟩
    refine ⟨e, member, ha, hb, ?_⟩
    obtain ⟨k, rfl⟩ := (mem_records_iff T e).mp member
    exact ⟨fullInterval, Finset.mem_singleton_self fullInterval,
      by change 0 ≤ (0 : Nat) ∧ 0 < 1; constructor <;> decide⟩

theorem uniqueParentAt (T x : Nat) : (finiteARG T).UniqueParentAt x := by
  intro child a b ha hb
  have ha' := (topology_iff T a child).mp ((finiteARG T).locus_edge_topology ha)
  have hb' := (topology_iff T b child).mp ((finiteARG T).locus_edge_topology hb)
  apply Prod.ext
  · apply Fin.ext
    omega
  · exact ha'.2.symm.trans hb'.2

/-- Every later generation on the same lane is reached at the covered locus. -/
theorem locus_reach_later (T : Nat) (a : Node T) :
    ∀ n (bound : n ≤ T), a.1.val < n →
      Reach ((finiteARG T).AtLocus 0) a
        (⟨n, Nat.lt_succ_of_le bound⟩, a.2) := by
  intro n
  induction n with
  | zero =>
      intro bound later
      omega
  | succ n ih =>
      intro bound later
      by_cases equal : a.1.val = n
      · apply Reach.edge
        apply (atLocus_iff T 0 _ _).mpr
        refine ⟨rfl, (topology_iff T _ _).mpr ⟨?_, rfl⟩⟩
        change n + 1 = a.1.val + 1
        omega
      · have bound' : n ≤ T := by omega
        have later' : a.1.val < n := by omega
        apply Reach.snoc (ih bound' later')
        apply (atLocus_iff T 0 _ _).mpr
        exact ⟨rfl, (topology_iff T _ _).mpr ⟨rfl, rfl⟩⟩

theorem sampleAncestral_zero (T : Nat) (a : Node T) :
    (finiteARG T).SampleAncestral 0 a := by
  let s : Node T := (⟨T, Nat.lt_succ_self T⟩, a.2)
  refine ⟨s, (sample_iff T s).mpr rfl, ?_⟩
  by_cases last : a.1.val = T
  · left
    apply Prod.ext
    · apply Fin.ext
      exact last
    · rfl
  · right
    apply locus_reach_later T a T (Nat.le_refl T)
    have bound := a.1.isLt
    omega

theorem sampleSupported (T : Nat) : (finiteARG T).SampleSupported := by
  intro x a b edge
  have position := ((atLocus_iff T x a b).mp edge).1
  subst x
  exact sampleAncestral_zero T b

end

end PairingGARG
