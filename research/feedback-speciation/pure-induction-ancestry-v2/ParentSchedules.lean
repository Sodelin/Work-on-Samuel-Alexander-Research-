import ExtinctionPedigree

/-! Actual finite-population parent-choice tables mapped to the Nat pedigree. -/
namespace ParentSchedules
open SpeciesBridge ExtinctionPedigree

abbrev Table (N : Nat) := Fin N → Fin 2 → Fin N
abbrev Schedule (N : Nat) := Nat → Table N

def childIndex (N : Nat) (hN : 0 < N) (v : Nat) : Fin N :=
  ⟨v % N, Nat.mod_lt v hN⟩

def edge (N : Nat) (hN : 0 < N) (p : Schedule N) (u v : Nat) : Prop :=
  v/N = u/N+1 ∧
  ∃ slot : Fin 2, (p (u/N) (childIndex N hN v) slot).val = u%N

theorem encoded_div (N : Nat) (hN : 0 < N) (n : Nat) (i : Fin N) :
    (i.val+n*N)/N = n := by
  rw [Nat.add_mul_div_right _ _ hN, Nat.div_eq_of_lt i.isLt]
  simp

theorem encoded_mod (N : Nat) (n : Nat) (i : Fin N) :
    (i.val+n*N)%N = i.val := by
  rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt i.isLt]

def model (N : Nat) (hN : 0 < N) (p : Schedule N) : Model where
  edge := edge N hN p
  generation v := v/N
  finitePast n := (finiteSupport_iff_bounded _).mpr
    ⟨n*N, fun _ hv => (Nat.div_lt_iff_lt_mul hN).mp hv⟩
  occupied n := ⟨n*N,Nat.mul_div_left n hN⟩
  edgeStep _ _ h := h.1
  parent v hv := by
    let i := p (v/N-1) (childIndex N hN v) (0 : Fin 2)
    let u := i.val+(v/N-1)*N
    have hu : u/N = v/N-1 := encoded_div N hN _ i
    have hum : u%N = i.val := encoded_mod N _ i
    refine ⟨u,?_⟩
    change v/N = u/N+1 ∧ _
    refine ⟨by omega, (0 : Fin 2), ?_⟩
    rw [hu,hum]

def constantTable {N : Nat} (pair : Fin 2 → Fin N) : Table N :=
  fun _ slot => pair slot

theorem constant_table_sync (N : Nat) (hN : 0 < N) (p : Schedule N)
    (t : Nat) (pair : Fin 2 → Fin N) (hp : p t = constantTable pair) :
    (model N hN p).Sync t (t+1) := by
  apply (model N hN p).common_parents_sync t
  intro u v w hu hv hw
  change u/N = t at hu
  change v/N = t+1 at hv
  change w/N = t+1 at hw
  change (v/N = u/N+1 ∧ _) ↔ (w/N = u/N+1 ∧ _)
  simp [hu,hv,hw,hp,constantTable]

theorem recurrent_constant_table_iap (N : Nat) (hN : 0 < N)
    (p : Schedule N) (pair : Fin 2 → Fin N)
    (hp : ∀ K, ∃ t, K ≤ t ∧ p t = constantTable pair) :
    IAP (model N hN p).edge Whole := by
  apply (model N hN p).late_sync_every_subset_iap
  intro K
  obtain ⟨t,ht,hp'⟩ := hp K
  exact ⟨t,t+1,ht,constant_table_sync N hN p t pair hp'⟩

theorem constant_table_resolves_older (N : Nat) (hN : 0 < N)
    (p : Schedule N) (t u : Nat) (pair : Fin 2 → Fin N)
    (hp : p t = constantTable pair) (hu : u/N < t) :
    (model N hN p).ResolvedFrom u (t+1) := by
  let G := model N hN p
  have hs : G.Sync t (t+1) := constant_table_sync N hN p t pair hp
  rcases G.sync_resolves_cohort (u := u) hs hu with hn | ha
  · exact Or.inl (G.none_cohort_persists (by change u/N < t+1; omega) hn)
  · exact Or.inr (G.all_cohort_persists ha)

end ParentSchedules
#print axioms ParentSchedules.encoded_div
#print axioms ParentSchedules.encoded_mod
#print axioms ParentSchedules.constant_table_sync
#print axioms ParentSchedules.recurrent_constant_table_iap
#print axioms ParentSchedules.constant_table_resolves_older
