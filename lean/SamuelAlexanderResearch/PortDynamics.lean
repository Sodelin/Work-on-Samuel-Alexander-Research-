import SamuelAlexanderResearch.FinitePhasePaths

/-!
# Crossing ports and periodic schedules

The slot lifecycle is explicit: surviving slots do not move, selected tokens
are consumed before their replacements are inserted, and replacements carry
the current birth as their source. Periodicity includes replacement labels.
No universality or quotient-language premise is used below.
-/

namespace PortDynamics

universe u

theorem nat_least (P : Nat → Prop) (nonempty : ∃ n, P n) :
    ∃ n, P n ∧ ∀ m, m < n → ¬ P m := by
  classical
  obtain ⟨n, hn⟩ := nonempty
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases smaller : ∃ m, m < n ∧ P m
    · obtain ⟨m, hm, hp⟩ := smaller
      exact ih m hm hp
    · exact ⟨n, hn, fun m hm hp => smaller ⟨m, hm, hp⟩⟩

theorem nat_greatest_below (P : Nat → Prop) (bound : Nat)
    (nonempty : ∃ n, n < bound ∧ P n) :
    ∃ n, n < bound ∧ P n ∧ ∀ m, m < bound → P m → m ≤ n := by
  classical
  induction bound with
  | zero => obtain ⟨n, hn, _⟩ := nonempty; omega
  | succ bound ih =>
    by_cases hb : P bound
    · exact ⟨bound, by omega, hb, by omega⟩
    · have hx : ∃ n, n < bound ∧ P n := by
        obtain ⟨n, hn, hp⟩ := nonempty
        refine ⟨n, ?_, hp⟩
        by_cases h : n = bound
        · exact False.elim (hb (h ▸ hp))
        · omega
      obtain ⟨n, hn, hp, hmax⟩ := ih hx
      refine ⟨n, by omega, hp, ?_⟩
      intro m hm hpm
      have : m < bound := by
        by_cases h : m = bound
        · exact False.elim (hb (h ▸ hpm))
        · omega
      exact hmax m this hpm

structure Schedule (C : Nat) (A : Type u) where
  selected : Nat → Fin C → Prop
  newLabel : Nat → Fin C → A

structure Token (A : Type u) where
  source : Nat
  label : A

noncomputable section

local instance (P : Prop) : Decidable P := Classical.propDecidable P

noncomputable def run {C : Nat} {A : Type u} (S : Schedule C A)
    (base : Nat) (initial : Fin C → Token A) : Nat → Fin C → Token A
  | 0 => initial
  | n + 1 => fun i => if S.selected n i then
      ⟨base + n, S.newLabel n i⟩ else run S base initial n i

def Fair {C : Nat} {A : Type u} (S : Schedule C A) : Prop :=
  ∀ n i, ∃ m, n ≤ m ∧ S.selected m i

def PeriodicAfter {C : Nat} {A : Type u} (S : Schedule C A)
    (M p : Nat) : Prop :=
  ∀ n, M ≤ n → ∀ i,
    (S.selected (n + p) i ↔ S.selected n i) ∧
    (S.selected n i → S.newLabel (n + p) i = S.newLabel n i)

def NextUse {C : Nat} {A : Type u} (S : Schedule C A)
    (n m : Nat) (i : Fin C) : Prop :=
  n < m ∧ S.selected m i ∧ ∀ t, n < t → t < m → ¬ S.selected t i

def BornEdge {C : Nat} {A : Type u} (S : Schedule C A)
    (n m : Nat) (a : A) : Prop :=
  ∃ i, S.selected n i ∧ NextUse S n m i ∧ S.newLabel n i = a

def DecodedEdge {C : Nat} {A : Type u} (S : Schedule C A)
    (base : Nat) (initial : Fin C → Token A) (u v : Nat) (a : A) : Prop :=
  ∃ n i, v = base + n ∧ S.selected n i ∧
    (run S base initial n i).source = u ∧ (run S base initial n i).label = a

theorem next_exists {C : Nat} {A : Type u} (S : Schedule C A)
    (fair : Fair S) (n : Nat) (i : Fin C) : ∃ m, NextUse S n m i := by
  obtain ⟨m, hm, hs⟩ := fair (n+1) i
  obtain ⟨r, hr, hmin⟩ := nat_least (fun t => n < t ∧ S.selected t i)
    ⟨m, by omega, hs⟩
  exact ⟨r, hr.1, hr.2, fun t hnt htr hst => hmin t htr ⟨hnt, hst⟩⟩

theorem next_unique {C : Nat} {A : Type u} {S : Schedule C A}
    {n m r : Nat} {i : Fin C} (hm : NextUse S n m i)
    (hr : NextUse S n r i) : m = r := by
  by_cases h : m < r
  · exact False.elim (hr.2.2 m hm.1 h hm.2.1)
  · by_cases h' : r < m
    · exact False.elim (hm.2.2 r hr.1 h' hr.2.1)
    · omega

theorem next_span_bound {C : Nat} {A : Type u} {S : Schedule C A}
    {M p n m : Nat} (hp : 0 < p) (period : PeriodicAfter S M p)
    (hn : M ≤ n) {i : Fin C} (hnext : NextUse S n m i) : m ≤ n + p := by
  by_cases h : m ≤ n+p
  · exact h
  · have hj : n < m-p := by omega
    have hM : M ≤ m-p := by omega
    have he : m-p+p = m := by omega
    have hs : S.selected (m-p) i := by
      apply (period (m-p) hM i).1.mp
      simpa only [he] using hnext.2.1
    exact False.elim (hnext.2.2 (m-p) hj (by omega) hs)

theorem next_shift_iff {C : Nat} {A : Type u} {S : Schedule C A}
    {M p n m : Nat} (period : PeriodicAfter S M p) (hn : M ≤ n)
    (i : Fin C) : NextUse S (n+p) (m+p) i ↔ NextUse S n m i := by
  constructor
  · intro h
    have hnm : n < m := by have := h.1; omega
    refine ⟨hnm, (period m (by omega) i).1.mp h.2.1, ?_⟩
    intro t hnt htm hs
    exact h.2.2 (t+p) (by omega) (by omega)
      ((period t (by omega) i).1.mpr hs)
  · intro h
    refine ⟨by have := h.1; omega,
      (period m (by have := h.1; omega) i).1.mpr h.2.1, ?_⟩
    intro t hnt htm hs
    have ht : M ≤ t-p := by omega
    have he : t-p+p = t := by omega
    have hsel : S.selected (t-p) i := (period (t-p) ht i).1.mp (by simpa [he] using hs)
    exact h.2.2 (t-p) (by omega) (by omega) hsel

theorem bornEdge_shift_iff {C : Nat} {A : Type u} {S : Schedule C A}
    {M p n m : Nat} (period : PeriodicAfter S M p) (hn : M ≤ n) (a : A) :
    BornEdge S (n+p) (m+p) a ↔ BornEdge S n m a := by
  constructor
  · rintro ⟨i, hs, hx, ha⟩
    have hs' := (period n hn i).1.mp hs
    exact ⟨i, hs', (next_shift_iff period hn i).mp hx,
      (period n hn i).2 hs' ▸ ha⟩
  · rintro ⟨i, hs, hx, ha⟩
    refine ⟨i, (period n hn i).1.mpr hs, (next_shift_iff period hn i).mpr hx, ?_⟩
    exact ((period n hn i).2 hs).trans ha

/-- The actual token is unchanged until the next consumption. -/
theorem token_survives {C : Nat} {A : Type u} (S : Schedule C A)
    (base : Nat) (initial : Fin C → Token A) {n m : Nat} {i : Fin C}
    (hnm : n < m) (born : S.selected n i)
    (quiet : ∀ t, n < t → t < m → ¬ S.selected t i) :
    run S base initial m i = ⟨base+n, S.newLabel n i⟩ := by
  classical
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases h : n = m
    · subst m
      simp only [run, if_pos born]
    · have hnm' : n < m := by omega
      have notSelected : ¬ S.selected m i := quiet m hnm' (by omega)
      simp only [run, if_neg notSelected]
      exact ih hnm' (fun t hnt htm => quiet t hnt (by omega))

theorem bornEdge_decodes {C : Nat} {A : Type u} (S : Schedule C A)
    (base : Nat) (initial : Fin C → Token A) {n m : Nat} {a : A}
    (edge : BornEdge S n m a) : DecodedEdge S base initial (base+n) (base+m) a := by
  obtain ⟨i, hn, hm, ha⟩ := edge
  have token := token_survives S base initial hm.1 hn hm.2.2
  exact ⟨m, i, rfl, hm.2.1, by rw [token], by rw [token]; exact ha⟩

/-- Incoming coverage is checked on the labels of actual consumed tokens. -/
def IncomingCoverage {C : Nat} {A : Type u} (S : Schedule C A)
    (base : Nat) (initial : Fin C → Token A) : Prop :=
  ∀ n a, ∃ i, S.selected n i ∧ (run S base initial n i).label = a

theorem periodic_late_incoming {C : Nat} {A : Type u} {S : Schedule C A}
    (base : Nat) (initial : Fin C → Token A) {M p : Nat}
    (hp : 0 < p) (period : PeriodicAfter S M p)
    (coverage : IncomingCoverage S base initial) (v : Nat) (hv : M+p ≤ v) (a : A) :
    ∃ n, M ≤ n ∧ BornEdge S n v a := by
  obtain ⟨i, hsel, ha⟩ := coverage v a
  have hM : M ≤ v-p := by omega
  have he : v-p+p = v := by omega
  have old : S.selected (v-p) i := (period (v-p) hM i).1.mp (by simpa [he] using hsel)
  obtain ⟨n, hnv, hn, hmax⟩ := nat_greatest_below
    (fun n => M ≤ n ∧ S.selected n i) v ⟨v-p, by omega, hM, old⟩
  have quiet : ∀ t, n < t → t < v → ¬ S.selected t i := by
    intro t hnt htv hst
    have := hmax t htv ⟨by have := hn.1; omega, hst⟩
    omega
  have token := token_survives S base initial hnv hn.2 quiet
  refine ⟨n, hn.1, i, hn.2, ⟨hnv, hsel, quiet⟩, ?_⟩
  simpa only [token] using ha

theorem bornEdge_shift_mul {C : Nat} {A : Type u} {S : Schedule C A}
    {M p n m : Nat} (period : PeriodicAfter S M p) (hn : M ≤ n)
    (q : Nat) (a : A) :
    BornEdge S (n+p*q) (m+p*q) a ↔ BornEdge S n m a := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ]
    have hx := bornEdge_shift_iff (m := m+p*q) period
      (show M ≤ n+p*q by omega) a
    simpa only [Nat.add_assoc] using hx.trans ih

theorem birth_decomposition {M p v : Nat} (hv : M ≤ v) :
    M+(v-M)%p+p*((v-M)/p) = v := by
  have h := Nat.mod_add_div (v-M) p
  omega

theorem normalize_bornEdge {C : Nat} {A : Type u} {S : Schedule C A}
    {M p v w : Nat} (period : PeriodicAfter S M p) (hv : M ≤ v)
    {a : A} (edge : BornEdge S v w a) :
    BornEdge S (M+(v-M)%p) (M+(v-M)%p+(w-v)) a := by
  have hvw : v < w := by obtain ⟨_, _, hx, _⟩ := edge; exact hx.1
  have hd := birth_decomposition (p := p) hv
  apply (bornEdge_shift_mul period (show M ≤ M+(v-M)%p by omega)
    ((v-M)/p) a).mp
  have htarget : M+(v-M)%p+(w-v)+p*((v-M)/p) = w := by omega
  simpa only [hd, htarget] using edge

/-- A phase edge retains its positive displacement, not just residue adjacency. -/
def PhaseEdge {C : Nat} {A : Type u} (S : Schedule C A) (M p : Nat)
    (r q : Fin p) (a : A) : Prop :=
  ∃ d, 0 < d ∧ d ≤ p ∧
    BornEdge S (M+r.val) (M+r.val+d) a ∧ q.val = (r.val+d)%p

theorem phase_incoming {C : Nat} {A : Type u} {S : Schedule C A}
    (base : Nat) (initial : Fin C → Token A) {M p : Nat}
    (hp : 0 < p) (period : PeriodicAfter S M p)
    (coverage : IncomingCoverage S base initial) (q : Fin p) (a : A) :
    ∃ r, PhaseEdge S M p r q a := by
  let v := M+p+q.val
  obtain ⟨n, hn, edge⟩ := periodic_late_incoming base initial hp period coverage
    v (by dsimp [v]; omega) a
  obtain ⟨i, hs, hx, ha⟩ := edge
  have hnv := hx.1
  have hspan := next_span_bound hp period hn hx
  let r : Fin p := ⟨(n-M)%p, Nat.mod_lt _ hp⟩
  refine ⟨r, v-n, by omega, by omega,
    normalize_bornEdge period hn ⟨i, hs, hx, ha⟩, ?_⟩
  have hd := birth_decomposition (p := p) hn
  have he : (n-M)%p+(v-n)+p*((n-M)/p) = p+q.val := by dsimp [v] at *; omega
  have hmod := congrArg (fun x => x%p) he
  have hclean : ((n-M)%p+(v-n))%p = q.val := by
    simpa only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.zero_mul,
      Nat.zero_mod, Nat.add_zero, Nat.zero_add, Nat.mod_mod,
      Nat.mod_eq_of_lt q.isLt] using hmod
  exact hclean.symm

def turns {p : Nat} (phase : Nat → Fin p) (jump : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => turns phase jump n + ((phase n).val+jump n)/p

/-- Every infinite quotient path lifts to actual increasing natural birth indices. -/
theorem lift_phase_path {C : Nat} {A : Type u} {S : Schedule C A}
    {M p : Nat} (period : PeriodicAfter S M p) (s : Nat → A)
    (phase : Nat → Fin p)
    (edges : ∀ n, PhaseEdge S M p (phase n) (phase (n+1)) (s n)) :
    ∃ path : Nat → Nat, M ≤ path 0 ∧ path 0 < M+p ∧
      ∀ n, BornEdge S (path n) (path (n+1)) (s n) := by
  let jump := fun n => Classical.choose (edges n)
  have hstep : ∀ n, 0 < jump n ∧ jump n ≤ p ∧
      BornEdge S (M+(phase n).val) (M+(phase n).val+jump n) (s n) ∧
      (phase (n+1)).val = ((phase n).val+jump n)%p :=
    fun n => Classical.choose_spec (edges n)
  let path := fun n => M+(phase n).val+p*turns phase jump n
  have start : path 0 = M+(phase 0).val := by simp [path, turns]
  refine ⟨path, by rw [start]; omega, by rw [start]; have := (phase 0).isLt; omega, ?_⟩
  intro n
  have advance : path (n+1) = path n+jump n := by
    have hm := Nat.mod_add_div ((phase n).val+jump n) p
    have hnext := (hstep n).2.2.2
    dsimp [path]
    rw [turns, Nat.mul_add, hnext]
    omega
  have lifted := (bornEdge_shift_mul period
    (show M ≤ M+(phase n).val by omega) (turns phase jump n) (s n)).mpr
      (hstep n).2.2.1
  rw [advance]
  change BornEdge S (M+(phase n).val+p*turns phase jump n)
    (M+(phase n).val+p*turns phase jump n+jump n) (s n)
  have ht : M+(phase n).val+p*turns phase jump n+jump n =
      M+(phase n).val+jump n+p*turns phase jump n := by omega
  rw [ht]
  exact lifted

/-- Full periodic token schedules with actual incoming-label coverage realize
every infinite word. The finite quotient's incoming property is derived above. -/
theorem periodic_schedule_realizes {C : Nat} {A : Type} {S : Schedule C A}
    (base : Nat) (initial : Fin C → Token A) {M p : Nat}
    (hp : 0 < p) (period : PeriodicAfter S M p)
    (coverage : IncomingCoverage S base initial) (s : Nat → A) :
    ∃ path : Nat → Nat, base+M ≤ path 0 ∧ path 0 < base+M+p ∧
      ∀ n, DecodedEdge S base initial (path n) (path (n+1)) (s n) := by
  obtain ⟨phase, edges⟩ := FinitePhasePaths.realizes_all hp (PhaseEdge S M p)
    (phase_incoming base initial hp period coverage) s
  obtain ⟨path, hlo, hhi, hedges⟩ := lift_phase_path period s phase edges
  refine ⟨fun n => base+path n, ?_, ?_, ?_⟩
  · change base+M ≤ base+path 0
    omega
  · change base+path 0 < base+M+p
    omega
  intro n
  exact bornEdge_decodes S base initial (hedges n)

/-- Initial outstanding edges must have already-born sources. -/
def InitialOld {C : Nat} {A : Type u} (base : Nat)
    (initial : Fin C → Token A) : Prop := ∀ i, (initial i).source < base

theorem run_source_lt {C : Nat} {A : Type u} (S : Schedule C A)
    (base : Nat) (initial : Fin C → Token A) (old : InitialOld base initial)
    (n : Nat) (i : Fin C) : (run S base initial n i).source < base+n := by
  induction n with
  | zero => exact old i
  | succ n ih =>
    by_cases h : S.selected n i
    · simp only [run, if_pos h]
      omega
    · simp only [run, if_neg h]
      omega

theorem decoded_birth_order {C : Nat} {A : Type u} (S : Schedule C A)
    (base : Nat) (initial : Fin C → Token A) (old : InitialOld base initial)
    {u v : Nat} {a : A} (edge : DecodedEdge S base initial u v a) : u < v := by
  obtain ⟨n, i, hv, _, hu, _⟩ := edge
  have h := run_source_lt S base initial old n i
  omega

/-- A tail-born token remembers its unique insertion time and label. -/
theorem token_origin {C : Nat} {A : Type u} (S : Schedule C A)
    (base : Nat) (initial : Fin C → Token A) (old : InitialOld base initial)
    {n t : Nat} {i : Fin C} (source : (run S base initial t i).source = base+n) :
    n < t ∧ S.selected n i ∧ (run S base initial t i).label = S.newLabel n i ∧
      ∀ r, n < r → r < t → ¬ S.selected r i := by
  induction t with
  | zero =>
    have h := old i
    change (initial i).source = base+n at source
    omega
  | succ t ih =>
    by_cases ht : S.selected t i
    · simp only [run, if_pos ht] at source ⊢
      have he : t = n := by omega
      subst t
      exact ⟨by omega, ht, rfl, by intro r hr hr'; omega⟩
    · simp only [run, if_neg ht] at source ⊢
      obtain ⟨hnt, hn, ha, quiet⟩ := ih source
      refine ⟨by omega, hn, ha, ?_⟩
      intro r hnr hrt
      by_cases he : r = t
      · exact he ▸ ht
      · exact quiet r hnr (by omega)

/-- Exact inverse: decoding introduces no additional edges between tail births. -/
theorem decoded_born_iff {C : Nat} {A : Type u} (S : Schedule C A)
    (base : Nat) (initial : Fin C → Token A) (old : InitialOld base initial)
    (n m : Nat) (a : A) :
    DecodedEdge S base initial (base+n) (base+m) a ↔ BornEdge S n m a := by
  constructor
  · rintro ⟨t, i, hv, ht, hu, ha⟩
    have he : t = m := by omega
    subst t
    obtain ⟨hnm, hn, hl, quiet⟩ := token_origin S base initial old hu
    exact ⟨i, hn, ⟨hnm, ht, quiet⟩, hl.symm.trans ha⟩
  · exact bornEdge_decodes S base initial

/-- No birth consumes two pending edges having the same source. -/
def SimpleConsumption {C : Nat} {A : Type u} (S : Schedule C A)
    (base : Nat) (initial : Fin C → Token A) : Prop :=
  ∀ n i j, S.selected n i → S.selected n j →
    (run S base initial n i).source = (run S base initial n j).source → i = j

theorem decoded_label_unique {C : Nat} {A : Type u} (S : Schedule C A)
    (base : Nat) (initial : Fin C → Token A)
    (simple : SimpleConsumption S base initial) {u v : Nat} {a b : A}
    (ea : DecodedEdge S base initial u v a)
    (eb : DecodedEdge S base initial u v b) : a = b := by
  obtain ⟨n, i, hv, hi, hu, ha⟩ := ea
  obtain ⟨m, j, hv', hj, hu', hb⟩ := eb
  have he : m = n := by omega
  subst m
  have hij := simple n i j hi hj (hu.trans hu'.symm)
  subst j
  exact ha.symm.trans hb

/-- A fair schedule gives every selected birth slot a unique later child. -/
noncomputable def child {C : Nat} {A : Type u} (S : Schedule C A)
    (fair : Fair S) (n : Nat) (i : Fin C) : Nat :=
  Classical.choose (next_exists S fair n i)

theorem child_spec {C : Nat} {A : Type u} (S : Schedule C A)
    (fair : Fair S) (n : Nat) (i : Fin C) : NextUse S n (child S fair n i) i :=
  Classical.choose_spec (next_exists S fair n i)

/-- Distinct slots born at one birth have distinct children when consumption is simple. -/
theorem child_injective {C : Nat} {A : Type u} (S : Schedule C A)
    (base : Nat) (initial : Fin C → Token A) (fair : Fair S)
    (simple : SimpleConsumption S base initial) (n : Nat) (i j : Fin C)
    (hi : S.selected n i) (hj : S.selected n j)
    (same : child S fair n i = child S fair n j) : i = j := by
  have hx := child_spec S fair n i
  have hy := child_spec S fair n j
  rw [← same] at hy
  have ti := token_survives S base initial hx.1 hi hx.2.2
  have tj := token_survives S base initial hy.1 hj hy.2.2
  exact simple _ i j hx.2.1 hy.2.1 (by rw [ti, tj])

/-- Exact child characterization; coupled with `child_injective`, this is the
slot-to-child bijection underlying the outdegree count. -/
theorem decoded_child_iff {C : Nat} {A : Type u} (S : Schedule C A)
    (base : Nat) (initial : Fin C → Token A) (old : InitialOld base initial)
    (fair : Fair S) (n m : Nat) (a : A) :
    DecodedEdge S base initial (base+n) (base+m) a ↔
      ∃ i, S.selected n i ∧ child S fair n i = m ∧ S.newLabel n i = a := by
  rw [decoded_born_iff S base initial old]
  constructor
  · rintro ⟨i, hi, hm, ha⟩
    exact ⟨i, hi, next_unique (child_spec S fair n i) hm, ha⟩
  · rintro ⟨i, hi, hm, ha⟩
    exact ⟨i, hi, hm ▸ child_spec S fair n i, ha⟩

/-- Complete legality for k-input births. The chosen input map is a bijection
onto the selected slots; their actual labels are the k distinct labels. -/
structure Legal {C k : Nat} (S : Schedule C (Fin k)) (base : Nat)
    (initial : Fin C → Token (Fin k)) where
  old : InitialOld base initial
  simple : SimpleConsumption S base initial
  inputs : Nat → Fin k → Fin C
  selected_iff : ∀ n i, S.selected n i ↔ ∃ a, inputs n a = i
  incoming_label : ∀ n a, (run S base initial n (inputs n a)).label = a

theorem Legal.coverage {C k : Nat} {S : Schedule C (Fin k)} {base : Nat}
    {initial : Fin C → Token (Fin k)} (legal : Legal S base initial) :
    IncomingCoverage S base initial := by
  intro n a
  exact ⟨legal.inputs n a, (legal.selected_iff _ _).mpr ⟨a, rfl⟩,
    legal.incoming_label n a⟩

theorem Legal.inputs_injective {C k : Nat} {S : Schedule C (Fin k)} {base : Nat}
    {initial : Fin C → Token (Fin k)} (legal : Legal S base initial)
    (n : Nat) {a b : Fin k} (same : legal.inputs n a = legal.inputs n b) : a = b := by
  have ha := legal.incoming_label n a
  have hb := legal.incoming_label n b
  rw [same] at ha
  exact ha.symm.trans hb

/-- The k outgoing children are indexed injectively by the k consumed inputs. -/
theorem Legal.outgoing_children_injective {C k : Nat} {S : Schedule C (Fin k)}
    {base : Nat} {initial : Fin C → Token (Fin k)}
    (legal : Legal S base initial) (fair : Fair S) (n : Nat) {a b : Fin k}
    (same : child S fair n (legal.inputs n a) = child S fair n (legal.inputs n b)) :
    a = b := by
  apply legal.inputs_injective n
  exact child_injective S base initial fair legal.simple n _ _
    ((legal.selected_iff _ _).mpr ⟨a, rfl⟩)
    ((legal.selected_iff _ _).mpr ⟨b, rfl⟩) same

theorem Legal.exact_outgoing_children {C k : Nat} {S : Schedule C (Fin k)}
    {base : Nat} {initial : Fin C → Token (Fin k)}
    (legal : Legal S base initial) (fair : Fair S) (n m : Nat) :
    (∃ label, DecodedEdge S base initial (base+n) (base+m) label) ↔
      ∃ a : Fin k, child S fair n (legal.inputs n a) = m := by
  constructor
  · rintro ⟨label, he⟩
    obtain ⟨i, hi, hm, _⟩ := (decoded_child_iff S base initial legal.old fair n m label).mp he
    obtain ⟨a, ha⟩ := (legal.selected_iff n i).mp hi
    exact ⟨a, ha ▸ hm⟩
  · rintro ⟨a, ha⟩
    refine ⟨S.newLabel n (legal.inputs n a), ?_⟩
    apply (decoded_child_iff S base initial legal.old fair n m _).mpr
    exact ⟨legal.inputs n a, (legal.selected_iff _ _).mpr ⟨a, rfl⟩, ha, rfl⟩

theorem Legal.exact_incoming_parent {C k : Nat} {S : Schedule C (Fin k)}
    {base : Nat} {initial : Fin C → Token (Fin k)}
    (legal : Legal S base initial) (n u : Nat) (a : Fin k) :
    DecodedEdge S base initial u (base+n) a ↔
      (run S base initial n (legal.inputs n a)).source = u := by
  constructor
  · rintro ⟨m, i, hv, hi, hu, ha⟩
    have he : m = n := by omega
    subst m
    obtain ⟨b, hb⟩ := (legal.selected_iff n i).mp hi
    have hl := legal.incoming_label n b
    rw [hb] at hl
    have heq : b = a := hl.symm.trans ha
    have hia : legal.inputs n a = i := by rw [← heq]; exact hb
    rw [hia]
    exact hu
  · intro hu
    exact ⟨n, legal.inputs n a, rfl, (legal.selected_iff _ _).mpr ⟨a, rfl⟩,
      hu, legal.incoming_label n a⟩

theorem Legal.incoming_parents_injective {C k : Nat} {S : Schedule C (Fin k)}
    {base : Nat} {initial : Fin C → Token (Fin k)}
    (legal : Legal S base initial) (n : Nat) {a b : Fin k}
    (same : (run S base initial n (legal.inputs n a)).source =
      (run S base initial n (legal.inputs n b)).source) : a = b := by
  apply legal.inputs_injective n
  exact legal.simple n _ _ ((legal.selected_iff _ _).mpr ⟨a, rfl⟩)
    ((legal.selected_iff _ _).mpr ⟨b, rfl⟩) same

theorem periodic_schedule_realizes_strict {C : Nat} {A : Type} {S : Schedule C A}
    (base : Nat) (initial : Fin C → Token A) {M p : Nat}
    (hp : 0 < p) (period : PeriodicAfter S M p)
    (coverage : IncomingCoverage S base initial) (s : Nat → A) :
    ∃ path : Nat → Nat, base+M ≤ path 0 ∧ path 0 < base+M+p ∧
      ∀ n, path n < path (n+1) ∧
        DecodedEdge S base initial (path n) (path (n+1)) (s n) := by
  obtain ⟨phase, edges⟩ := FinitePhasePaths.realizes_all hp (PhaseEdge S M p)
    (phase_incoming base initial hp period coverage) s
  obtain ⟨path, hlo, hhi, hedges⟩ := lift_phase_path period s phase edges
  refine ⟨fun n => base+path n, ?_, ?_, ?_⟩
  · change base+M ≤ base+path 0
    omega
  · change base+path 0 < base+M+p
    omega
  · intro n
    have he := hedges n
    have hlt : path n < path (n+1) := by
      obtain ⟨_, _, hx, _⟩ := he
      exact hx.1
    exact ⟨by change base+path n < base+path (n+1); omega,
      bornEdge_decodes S base initial he⟩

/-- Pending token consumption includes the current cut birth. -/
def PendingUse {C : Nat} {A : Type u} (S : Schedule C A)
    (n m : Nat) (i : Fin C) : Prop :=
  n ≤ m ∧ S.selected m i ∧ ∀ t, n ≤ t → t < m → ¬ S.selected t i

theorem pending_exists {C : Nat} {A : Type u} (S : Schedule C A)
    (fair : Fair S) (n : Nat) (i : Fin C) : ∃ m, PendingUse S n m i := by
  obtain ⟨m, hm, hmin⟩ := nat_least (fun t => n ≤ t ∧ S.selected t i) (fair n i)
  exact ⟨m, hm.1, hm.2, fun t hnt htm ht => hmin t htm ⟨hnt, ht⟩⟩

noncomputable def pendingChild {C : Nat} {A : Type u} (S : Schedule C A)
    (fair : Fair S) (n : Nat) (i : Fin C) : Nat :=
  Classical.choose (pending_exists S fair n i)

theorem pendingChild_spec {C : Nat} {A : Type u} (S : Schedule C A)
    (fair : Fair S) (n : Nat) (i : Fin C) : PendingUse S n (pendingChild S fair n i) i :=
  Classical.choose_spec (pending_exists S fair n i)

theorem pending_unique {C : Nat} {A : Type u} {S : Schedule C A}
    {n m r : Nat} {i : Fin C} (hm : PendingUse S n m i)
    (hr : PendingUse S n r i) : m = r := by
  by_cases h : m < r
  · exact False.elim (hr.2.2 m hm.1 h hm.2.1)
  · by_cases h' : r < m
    · exact False.elim (hm.2.2 r hr.1 h' hr.2.1)
    · omega

theorem pending_survives {C : Nat} {A : Type u} (S : Schedule C A)
    (base : Nat) (initial : Fin C → Token A) {n m : Nat} {i : Fin C}
    (hnm : n ≤ m) (quiet : ∀ t, n ≤ t → t < m → ¬ S.selected t i) :
    run S base initial m i = run S base initial n i := by
  induction m with
  | zero =>
    have he : n = 0 := by omega
    subst n
    rfl
  | succ m ih =>
    by_cases he : n = m+1
    · rw [he]
    · have hnm' : n ≤ m := by omega
      have hs := quiet m hnm' (by omega)
      simp only [run, if_neg hs]
      exact ih hnm' (fun t ht hm => quiet t ht (by omega))

/-- A token older than a cut cannot have been inserted after that cut. -/
theorem old_token_quiet {C : Nat} {A : Type u} (S : Schedule C A)
    (base : Nat) (initial : Fin C → Token A) {n m : Nat} {i : Fin C}
    (hnm : n ≤ m) (old : (run S base initial m i).source < base+n) :
    ∀ t, n ≤ t → t < m → ¬ S.selected t i := by
  induction m with
  | zero => intro t ht htm; omega
  | succ m ih =>
    by_cases he : n = m+1
    · intro t ht htm; omega
    · have hnm' : n ≤ m := by omega
      have hs : ¬ S.selected m i := by
        intro hs
        simp only [run, if_pos hs] at old
        omega
      simp only [run, if_neg hs] at old
      have quiet := ih hnm' old
      intro t ht htm
      by_cases he : t = m
      · exact he ▸ hs
      · exact quiet t ht (by omega)

/-- Every current slot decodes to an actual crossing edge if it is eventually consumed. -/
theorem pending_crosses {C : Nat} {A : Type u} (S : Schedule C A)
    (base : Nat) (initial : Fin C → Token A) (old : InitialOld base initial)
    (fair : Fair S) (n : Nat) (i : Fin C) :
    (run S base initial n i).source < base+n ∧
    base+n ≤ base+pendingChild S fair n i ∧
    DecodedEdge S base initial (run S base initial n i).source
      (base+pendingChild S fair n i) (run S base initial n i).label := by
  have hx := pendingChild_spec S fair n i
  have ht := pending_survives S base initial hx.1 hx.2.2
  exact ⟨run_source_lt S base initial old n i, by have := hx.1; omega,
    pendingChild S fair n i, i, rfl, hx.2.1, by rw [ht], by rw [ht]⟩

/-- Every actual crossing edge comes from a current slot; no phantom edge is needed. -/
theorem crossing_from_slot {C : Nat} {A : Type u} (S : Schedule C A)
    (base : Nat) (initial : Fin C → Token A) (fair : Fair S)
    {n u v : Nat} {a : A} (hu : u < base+n) (hv : base+n ≤ v)
    (edge : DecodedEdge S base initial u v a) :
    ∃ i, (run S base initial n i).source = u ∧
      base+pendingChild S fair n i = v ∧ (run S base initial n i).label = a := by
  obtain ⟨m, i, hm, hs, hsource, hl⟩ := edge
  have hnm : n ≤ m := by omega
  have old : (run S base initial m i).source < base+n := by omega
  have quiet := old_token_quiet S base initial hnm old
  have ht := pending_survives S base initial hnm quiet
  have he := pending_unique (pendingChild_spec S fair n i) ⟨hnm, hs, quiet⟩
  exact ⟨i, ht ▸ hsource, by omega, ht ▸ hl⟩

/-- Current slots represent distinct source-child pairs, giving the exact C-edge cut. -/
theorem crossing_slots_injective {C : Nat} {A : Type u} (S : Schedule C A)
    (base : Nat) (initial : Fin C → Token A) (fair : Fair S)
    (simple : SimpleConsumption S base initial) (n : Nat) (i j : Fin C)
    (hs : (run S base initial n i).source = (run S base initial n j).source)
    (hc : pendingChild S fair n i = pendingChild S fair n j) : i = j := by
  have hx := pendingChild_spec S fair n i
  have hy := pendingChild_spec S fair n j
  rw [← hc] at hy
  have ti := pending_survives S base initial hx.1 hx.2.2
  have tj := pending_survives S base initial hy.1 hy.2.2
  exact simple _ i j hx.2.1 hy.2.1 (by rw [ti, tj]; exact hs)

theorem pending_span_bound {C : Nat} {A : Type u} {S : Schedule C A}
    {M p n m : Nat} (hp : 0 < p) (period : PeriodicAfter S M p)
    (hn : M ≤ n) {i : Fin C} (pending : PendingUse S n m i) : m < n+p := by
  by_cases h : m < n+p
  · exact h
  · have hM : M ≤ m-p := by omega
    have he : m-p+p = m := by omega
    have hs : S.selected (m-p) i := (period (m-p) hM i).1.mp
      (by simpa only [he] using pending.2.1)
    exact False.elim (pending.2.2 (m-p) (by omega) (by omega) hs)

/-- Fair periodic schedules consume every current slot within one period. -/
theorem fair_period_block {C : Nat} {A : Type u} {S : Schedule C A}
    (fair : Fair S) {M p : Nat} (hp : 0 < p) (period : PeriodicAfter S M p)
    (n : Nat) (hn : M ≤ n) (i : Fin C) :
    ∃ m, n ≤ m ∧ m < n+p ∧ S.selected m i := by
  have hx := pendingChild_spec S fair n i
  exact ⟨pendingChild S fair n i, hx.1, pending_span_bound hp period hn hx, hx.2.1⟩

/-- Explicit carryover clearance: every token after one whole period was
inserted during that period, including its correct source and label. -/
theorem fair_period_flush {C : Nat} {A : Type u} {S : Schedule C A}
    (base : Nat) (initial : Fin C → Token A) (fair : Fair S)
    {M p : Nat} (hp : 0 < p) (period : PeriodicAfter S M p)
    (n : Nat) (hn : M ≤ n) (i : Fin C) :
    ∃ m, n ≤ m ∧ m < n+p ∧ S.selected m i ∧
      run S base initial (n+p) i = ⟨base+m, S.newLabel m i⟩ := by
  obtain ⟨r, hnr, hr, hs⟩ := fair_period_block fair hp period n hn i
  obtain ⟨m, hm, hsel, hmax⟩ := nat_greatest_below
    (fun m => n ≤ m ∧ S.selected m i) (n+p) ⟨r, hr, hnr, hs⟩
  refine ⟨m, hsel.1, hm, hsel.2, token_survives S base initial hm hsel.2 ?_⟩
  intro t hmt htn hst
  have h := hmax t htn ⟨by have := hsel.1; omega, hst⟩
  omega

theorem Legal.periodic_realizes {C k : Nat} {S : Schedule C (Fin k)}
    {base : Nat} {initial : Fin C → Token (Fin k)}
    (legal : Legal S base initial) {M p : Nat} (hp : 0 < p)
    (period : PeriodicAfter S M p) (s : Nat → Fin k) :
    ∃ path : Nat → Nat, base+M ≤ path 0 ∧ path 0 < base+M+p ∧
      ∀ n, path n < path (n+1) ∧
        DecodedEdge S base initial (path n) (path (n+1)) (s n) :=
  periodic_schedule_realizes_strict base initial hp period legal.coverage s

#print axioms periodic_schedule_realizes_strict
#print axioms decoded_born_iff
#print axioms Legal.exact_incoming_parent
#print axioms Legal.incoming_parents_injective
#print axioms Legal.exact_outgoing_children
#print axioms Legal.outgoing_children_injective
#print axioms pending_crosses
#print axioms crossing_from_slot
#print axioms crossing_slots_injective
#print axioms fair_period_flush

end

end PortDynamics
