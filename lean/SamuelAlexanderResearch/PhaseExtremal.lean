import SamuelAlexanderResearch.PhaseShift

/-! Actual extremal paths and exact equality for shifted Thue--Morse targets. -/

namespace PhaseExtremal

open BinaryAvoidance QuantitativeAvoidance ThueMorseBits

def Part (phase : Nat) (path : Nat → Nat) (len : Nat) : Prop :=
  ∀ i, i < len → BinaryAvoidance.Edge t (path i) (path (i+1)) (t (phase+i))

def Segment (phase len x y : Nat) : Prop :=
  ∃ path : Nat → Nat, path 0 = x ∧ path len = y ∧ Part phase path len

def joinPath (front tail : Nat → Nat) (len : Nat) : Nat → Nat :=
  fun k => if k ≤ len then front k else tail (k-len)

theorem join_early (front tail : Nat → Nat) (len k : Nat) (hk : k ≤ len) :
    joinPath front tail len k = front k := by simp [joinPath, hk]

theorem join_late (front tail : Nat → Nat) (len k : Nat) (hk : len ≤ k)
    (hj : front len = tail 0) : joinPath front tail len k = tail (k-len) := by
  by_cases he : k = len
  · subst k; simp [joinPath, hj]
  · simp [joinPath, show ¬ k ≤ len by omega]

theorem part_join (phase len more : Nat) (front tail : Nat → Nat)
    (hf : Part phase front len) (ht : Part (phase+len) tail more)
    (hj : front len = tail 0) : Part phase (joinPath front tail len) (len+more) := by
  intro k hk
  by_cases he : k < len
  · rw [join_early _ _ _ k (by omega), join_early _ _ _ (k+1) (by omega)]
    exact hf k he
  · rw [join_late _ _ _ k (by omega) hj, join_late _ _ _ (k+1) (by omega) hj]
    have h := ht (k-len) (by omega)
    have hi : k+1-len = (k-len)+1 := by omega
    have hp : phase+len+(k-len) = phase+k := by omega
    simpa only [hi, hp] using h

theorem segment_append (phase len more x y z : Nat)
    (hf : Segment phase len x y) (ht : Segment (phase+len) more y z) :
    Segment phase (len+more) x z := by
  obtain ⟨front, hzero, hend, hfront⟩ := hf
  obtain ⟨tail, tzero, tend, htail⟩ := ht
  have hj : front len = tail 0 := by omega
  refine ⟨joinPath front tail len, by simpa [joinPath] using hzero, ?_,
    part_join phase len more front tail hfront htail hj⟩
  rw [join_late _ _ _ (len+more) (by omega) hj]
  simpa using tend

theorem segment_zero (phase x : Nat) : Segment phase 0 x x :=
  ⟨fun _ => x, rfl, rfl, fun i hi => by omega⟩

theorem extend_part (phase len more : Nat) (front : Nat → Nat) (y : Nat)
    (hf : Part phase front len) (ht : Segment (phase+len) more (front len) y) :
    ∃ path : Nat → Nat, path 0 = front 0 ∧ path (len+more) = y ∧
      Part phase path (len+more) ∧ ∀ k, k ≤ len → path k = front k := by
  obtain ⟨tail, hzero, hend, htail⟩ := ht
  refine ⟨joinPath front tail len, by simp [joinPath], ?_,
    part_join phase len more front tail hf htail hzero.symm, join_early front tail len⟩
  rw [join_late _ _ _ (len+more) (by omega) hzero.symm]
  simpa using hend

theorem part_ones (phase x len : Nat) (hx : 1 ≤ x)
    (hbit : ∀ i, i < len → t (x+i+1) = t (phase+i)) :
    Part phase (fun i => x+i) len := by
  intro i hi
  dsimp only
  refine ⟨by omega, Or.inl ⟨by omega, ?_⟩⟩
  rw [SharpThueMorse.binary_row_eq]
  have he : x+(i+1) = x+i+1 := by omega
  rw [he, hbit i hi]

theorem part_twos (phase x len : Nat)
    (hbit : ∀ i, i < len → (!(t (x+2*i+2))) = t (phase+i)) :
    Part phase (fun i => x+2*i) len := by
  intro i hi
  dsimp only
  refine ⟨by omega, Or.inr ⟨by omega, ?_⟩⟩
  rw [SharpThueMorse.binary_row_eq]
  have he : x+2*(i+1) = x+2*i+2 := by omega
  rw [he, hbit i hi]

theorem segment_ones (phase x len : Nat) (hx : 1 ≤ x)
    (hbit : ∀ i, i < len → t (x+i+1) = t (phase+i)) :
    Segment phase len x (x+len) :=
  ⟨fun i => x+i, by simp, rfl, part_ones phase x len hx hbit⟩

theorem segment_twos (phase x len : Nat)
    (hbit : ∀ i, i < len → (!(t (x+2*i+2))) = t (phase+i)) :
    Segment phase len x (x+2*len) :=
  ⟨fun i => x+2*i, by simp, rfl, part_twos phase x len hbit⟩

theorem xor_cancel_equal (a b c : Bool) (hab : a = b) :
    Bool.xor a c = Bool.xor b c := by rw [hab]

theorem t_shift_power (n k : Nat) (hk : k < 2^n) :
    t (k+2^n) = !(t k) := by
  have h := t_dyadic_block 1 n k hk
  simpa [Nat.add_comm] using h

theorem staircase_bits (d : Nat) :
    t (8 * 2^(d+2) + 3) = true ∧ t (3 * 2^(d+2) + 2) = true ∧
    t (4 * 2^(d+2) + 2) = false ∧ t (3 * 2^(d+2) + 3) = false := by
  have hb : 3 < 2^(d+2) := by have := index_lt_two_pow d; simp only [Nat.pow_succ]; omega
  have h1 := t_dyadic_block 8 (d+2) 3 hb
  have h2 := t_dyadic_block 3 (d+2) 2 (by omega)
  have h3 := t_dyadic_block 4 (d+2) 2 (by omega)
  have h4 := t_dyadic_block 3 (d+2) 3 hb
  simpa using And.intro h1 (And.intro h2 (And.intro h3 h4))

theorem staircase_step (m d : Nat) :
    Segment (3*2^(m+d+2)+2*2^m) (2*2^m)
      (8*2^(m+d+2)+3*2^m-1) (8*2^(m+d+2)+6*2^m-1) := by
  let q := 2^(m+d+2)
  let r := 2^m
  let M := 2^(d+2)
  have hr : 0 < r := Nat.two_pow_pos m
  have hq : q = M*r := by
    dsimp [q, r, M]
    rw [show m+d+2 = (d+2)+m by omega, Nat.pow_add]
  have hb := staircase_bits d
  have hones := segment_ones (3*q+2*r) (8*q+3*r-1) r (by omega) (by
    intro i hi
    have he : (8*q+3*r-1)+i+1 = (8*M+3)*r+i := by
      simp only [Nat.add_mul, Nat.mul_assoc, ← hq]
      omega
    have ht : (3*q+2*r)+i = (3*M+2)*r+i := by
      simp only [Nat.add_mul, Nat.mul_assoc, ← hq]
    rw [he, ht, t_dyadic_block _ m i hi, t_dyadic_block _ m i hi]
    simp only [show t (8*M+3) = true from hb.1, show t (3*M+2) = true from hb.2.1])
  have hones' : Segment (3*q+2*r) r (8*q+3*r-1) (8*q+4*r-1) := by
    have he : 8*q+3*r-1+r = 8*q+4*r-1 := by omega
    simpa only [he] using hones
  have htwos := segment_twos (3*q+3*r) (8*q+4*r-1) r (by
    intro i hi
    have he : (8*q+4*r-1)+2*i+2 = 2*((4*M+2)*r+i)+1 := by
      simp only [Nat.add_mul, Nat.mul_assoc, ← hq]
      omega
    have ht : (3*q+3*r)+i = (3*M+3)*r+i := by
      simp only [Nat.add_mul, Nat.mul_assoc, ← hq]
    rw [he, ht, t_double_add_one, Bool.not_not,
      t_dyadic_block _ m i hi, t_dyadic_block _ m i hi]
    simp only [show t (4*M+2) = false from hb.2.2.1,
      show t (3*M+3) = false from hb.2.2.2])
  have htwos' : Segment ((3*q+2*r)+r) r (8*q+4*r-1) (8*q+6*r-1) := by
    have he : 8*q+4*r-1+2*r = 8*q+6*r-1 := by omega
    have ht : (3*q+2*r)+r = 3*q+3*r := by omega
    simpa only [he, ht] using htwos
  have h := segment_append _ _ _ _ _ _ hones' htwos'
  have hl : r+r = 2*r := by omega
  simpa only [hl] using h

theorem staircase (d : Nat) : ∀ m,
    Segment (3*2^(m+d+1)+2*2^m) (2*(2^(m+d)-2^m))
      (8*2^(m+d+1)+3*2^m-1) (8*2^(m+d+1)+3*2^(m+d)-1) := by
  induction d with
  | zero =>
    intro m
    simpa using segment_zero (3*2^(m+1)+2*2^m) (8*2^(m+1)+3*2^m-1)
  | succ d ih =>
    intro m
    have hfirst := staircase_step m d
    have htail := ih (m+1)
    have he2 : m+1+d = m+d+1 := by omega
    simp only [he2] at htail
    have hfirst' : Segment (3*2^(m+d+2)+2*2^m) (2*2^m)
        (8*2^(m+d+2)+3*2^m-1) (8*2^(m+d+2)+6*2^m-1) := hfirst
    have ht : (3*2^(m+d+2)+2*2^m)+2*2^m = 3*2^(m+d+2)+2*(2^m*2) := by omega
    have hx : 8*2^(m+d+2)+6*2^m-1 = 8*2^(m+d+2)+3*(2^m*2)-1 := by omega
    have htail' : Segment ((3*2^(m+d+2)+2*2^m)+2*2^m)
        (2*(2^(m+d+1)-2^(m+1)))
        (8*2^(m+d+2)+6*2^m-1) (8*2^(m+d+2)+3*2^(m+d+1)-1) := by
      rw [ht, hx]
      simpa only [Nat.pow_succ] using htail
    have h := segment_append _ _ _ _ _ _ hfirst' htail'
    have hbound : 2^m ≤ 2^(m+d+1) := by
      apply Nat.pow_le_pow_right (by omega)
      omega
    have hl : 2*2^m + 2*(2^(m+d+1)-2^(m+1)) = 2*(2^(m+d+1)-2^m) := by
      have hb : 2^(m+1) ≤ 2^(m+d+1) := by
        apply Nat.pow_le_pow_right (by omega)
        omega
      rw [Nat.pow_succ] at *
      omega
    simpa only [show m+(d+1)+1 = m+d+2 by omega,
      show m+(d+1) = m+d+1 by omega, hl] using h

theorem head_remainder (n : Nat) :
    Segment (2*2^(n+1)-1) (2*2^(n+1)+1) (6*2^(n+1)-3)
      (8*2^(n+1)+3*2^n-1) := by
  let q := 2^(n+1)
  have hp : 2 ≤ q := by dsimp [q]; rw [Nat.pow_succ]; have := Nat.two_pow_pos n; omega
  have hthird := segment_ones (2*q-1) (6*q-3) 1 (by omega) (by
    intro i hi
    have hi0 : i = 0 := by omega
    subst i
    have hdest : 6*q-3+0+1 = 2*(3*q-1) := by omega
    have hleft : 3*q-1 = 2*q+(q-1) := by omega
    have hright : 2*q-1+0 = 1*q+(q-1) := by omega
    rw [hdest, t_double, hleft, hright,
      t_dyadic_block 2 (n+1) (q-1) (by omega),
      t_dyadic_block 1 (n+1) (q-1) (by omega)]
    simp)
  have hthird' : Segment (2*q-1) 1 (6*q-3) (6*q-2) := by
    have he : 6*q-3+1 = 6*q-2 := by omega
    simpa only [he] using hthird
  have hfourth := segment_twos (2*q) (6*q-2) (q+2) (by
    intro i hi
    have he : 6*q-2+2*i+2 = 2*(3*q+i) := by omega
    rw [he, t_double]
    have hn := SharpThueMorse.block_ne (n+1) 3 2 2 i (by
      intro j hj
      have hc : j = 0 ∨ j = 1 := by omega
      rcases hc with rfl | rfl <;> decide +kernel) (by change i < 2*q; omega)
    change t (3*q+i) ≠ t (2*q+i) at hn
    cases h1 : t (3*q+i) <;> cases h2 : t (2*q+i) <;> simp_all)
  have hfourth' : Segment ((2*q-1)+1) (q+2) (6*q-2) (8*q+2) := by
    have he : 6*q-2+2*(q+2) = 8*q+2 := by omega
    have ht : (2*q-1)+1 = 2*q := by omega
    simpa only [he, ht] using hfourth
  have h34 := segment_append _ _ _ _ _ _ hthird' hfourth'
  have hstairs := staircase n 0
  have hq : q = 2^n*2 := by dsimp [q]; rw [Nat.pow_succ]
  have hstairs' : Segment ((2*q-1)+(1+(q+2))) (q-2) (8*q+2)
      (8*q+3*2^n-1) := by
    have hp0 := Nat.two_pow_pos n
    have ht : (2*q-1)+(1+(q+2)) = 3*q+2 := by omega
    have hl : 2*(2^n-1) = q-2 := by omega
    have hx : 8*q+3*1-1 = 8*q+2 := by omega
    simpa only [Nat.zero_add, Nat.pow_zero, Nat.mul_one, ht, ← hl, ← hx] using hstairs
  have h := segment_append _ _ _ _ _ _ h34 hstairs'
  have hl : (1+(q+2))+(q-2) = 2*q+1 := by omega
  simpa only [hl] using h

/-- The complete four-q head, including its dyadic staircase. -/
theorem head_path (n : Nat) :
    ∃ path : Nat → Nat, path 0 = 3*2^(n+1)-1 ∧
      path (4*2^(n+1)) = 8*2^(n+1)+3*2^n-1 ∧ Part 0 path (4*2^(n+1)) ∧
      (∀ k, k ≤ 2^(n+1) → path k = 3*2^(n+1)-1+k) ∧
      path (2^(n+1)+1) = 4*2^(n+1)+1 := by
  let q := 2^(n+1)
  have hp : 2 ≤ q := by dsimp [q]; rw [Nat.pow_succ]; have := Nat.two_pow_pos n; omega
  let front := joinPath (fun i => 3*q-1+i) (fun i => 4*q-1+2*i) q
  have hone : Part 0 (fun i => 3*q-1+i) q := part_ones 0 (3*q-1) q (by omega) (by
    intro i hi
    have he : 3*q-1+i+1 = 3*q+i := by omega
    rw [he, t_dyadic_block 3 (n+1) i hi]
    simp)
  have htwo : Part (0+q) (fun i => 4*q-1+2*i) (q-1) := by
    apply part_twos
    intro i hi
    have he : 4*q-1+2*i+2 = 2*(2*q+i)+1 := by omega
    rw [he, t_double_add_one, Bool.not_not, Nat.zero_add,
      t_dyadic_block 2 (n+1) i (by omega)]
    have hbit := t_dyadic_block 1 (n+1) i (by omega : i < 2^(n+1))
    simpa using hbit.symm
  have hj : (fun i => 3*q-1+i) q = (fun i => 4*q-1+2*i) 0 := by dsimp only; omega
  have hfront : Part 0 front (2*q-1) := by
    have h := part_join 0 q (q-1) _ _ hone htwo hj
    have hl : q+(q-1) = 2*q-1 := by omega
    simpa only [hl] using h
  have hfrontend : front (2*q-1) = 6*q-3 := by
    dsimp only [front]
    rw [join_late (fun i => 3*q-1+i) (fun i => 4*q-1+2*i) q (2*q-1) (by omega) hj]
    omega
  have hrest : Segment (0+(2*q-1)) (2*q+1) (front (2*q-1))
      (8*q+3*2^n-1) := by
    rw [hfrontend, Nat.zero_add]
    exact head_remainder n
  obtain ⟨path, hzero, hend, hpart, hsame⟩ := extend_part 0 (2*q-1) (2*q+1) front _ hfront hrest
  have hl : (2*q-1)+(2*q+1) = 4*q := by omega
  rw [hl] at hend hpart
  refine ⟨path, ?_, hend, hpart, ?_, ?_⟩
  · change path 0 = 3*q-1
    rw [hzero]
    simp [front, joinPath]
  · intro k hk
    change path k = 3*q-1+k
    rw [hsame k (by omega)]
    simp only [front, joinPath, show k ≤ q from hk, if_true]
  · change path (q+1) = 4*q+1
    rw [hsame (q+1) (by omega)]
    simp only [front, joinPath, show ¬ q+1 ≤ q by omega, if_false]
    omega

theorem part_monotone (phase len : Nat) (path : Nat → Nat) (h : Part phase path len)
    (i j : Nat) (hij : i ≤ j) (hj : j ≤ len) : path i ≤ path j := by
  induction j with
  | zero =>
    have hi : i = 0 := by omega
    simp only [hi, Nat.le_refl]
  | succ j ih =>
    by_cases hi : i ≤ j
    · have hp := ih hi (by omega)
      have he := FiniteEditStability.edge_displacement t (path j) (path (j+1))
        (t (phase+j)) (h j (by omega))
      omega
    · have hi' : i = j+1 := by omega
      simp only [hi', Nat.le_refl]

theorem half_translate (n : Nat) (path : Nat → Nat)
    (hm : Part 0 path (8*2^n-3)) (hend : path (8*2^n-3) = 16*2^n-6) :
    Part (4*2^(n+1)) (fun i => path i+8*2^(n+1)) (8*2^n-3) := by
  let q := 2^(n+1)
  have hq : q = 2^n*2 := by dsimp [q]; rw [Nat.pow_succ]
  have hp := Nat.two_pow_pos n
  have hA : 4*q = 2^(n+3) := by dsimp [q]; simp only [Nat.pow_succ]; omega
  have hB : 8*q = 2^(n+4) := by dsimp [q]; simp only [Nat.pow_succ]; omega
  intro i hi
  have hw := part_monotone 0 (8*2^n-3) path hm (i+1) (8*2^n-3) (by omega) (by omega)
  rw [hend] at hw
  have hdest : t (path (i+1)+8*q) = !(t (path (i+1))) := by
    rw [hB]
    apply t_shift_power
    rw [← hB]
    omega
  have htime : t (4*q+i) = !(t i) := by
    rw [hA, Nat.add_comm]
    apply t_shift_power
    rw [← hA]
    omega
  have he := hm i hi
  simp only [Nat.zero_add] at he
  change BinaryAvoidance.Edge t (path i+8*q) (path (i+1)+8*q) (t (4*q+i))
  obtain ⟨hroot, (⟨hstep, hlabel⟩ | ⟨hstep, hlabel⟩)⟩ := he
  · refine ⟨by omega, Or.inl ⟨by omega, ?_⟩⟩
    rw [SharpThueMorse.binary_row_eq] at hlabel
    rw [SharpThueMorse.binary_row_eq, hdest, htime, hlabel]
  · refine ⟨by omega, Or.inr ⟨by omega, ?_⟩⟩
    rw [SharpThueMorse.binary_row_eq] at hlabel
    rw [SharpThueMorse.binary_row_eq, hdest, htime, hlabel]

/-- An actual extremal path, with its initial run proved pointwise. -/
theorem extremal_path (n : Nat) :
    ∃ path : Nat → Nat, path 0 = 3*2^n-1 ∧ path (8*2^n-3) = 16*2^n-6 ∧
      Part 0 path (8*2^n-3) ∧
      (∀ k, k ≤ 2^n → path k = 3*2^n-1+k) ∧
      (0 < n → path (2^n+1) = 4*2^n+1) := by
  induction n with
  | zero =>
    let path := fun k => if k ≤ 2 then 2+k else 2*k
    refine ⟨path, by simp [path], by simp [path], ?_, ?_, by omega⟩
    · intro i hi
      have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by simp only [Nat.pow_zero] at hi; omega
      rcases hc with rfl | rfl | rfl | rfl | rfl <;>
        simp [path, BinaryAvoidance.Edge, SharpThueMorse.binary_row_eq]
    · intro k hk
      simp only [Nat.pow_zero] at hk ⊢
      simp [path, show k ≤ 2 by omega]
  | succ n ih =>
    let q := 2^(n+1)
    have hq : q = 2^n*2 := by dsimp [q]; rw [Nat.pow_succ]
    have hp := Nat.two_pow_pos n
    obtain ⟨half, hz, he, hm, _, _⟩ := ih
    obtain ⟨head, hzhead, hehead, hmhead, hfirst, hnext⟩ := head_path n
    have htail : Segment (0+4*q) (8*2^n-3) (head (4*q)) (16*q-6) := by
      refine ⟨fun i => half i+8*q, ?_, ?_, ?_⟩
      · dsimp only
        rw [hz, hehead]
        omega
      · dsimp only
        rw [he]
        omega
      · simpa only [Nat.zero_add] using half_translate n half hm he
    obtain ⟨path, hzero, hend, hmatch, hsame⟩ := extend_part 0 (4*q) (8*2^n-3) head _ hmhead htail
    have hlen : 4*q+(8*2^n-3) = 8*q-3 := by omega
    rw [hlen] at hend hmatch
    refine ⟨path, hzero.trans hzhead, hend, hmatch, ?_, ?_⟩
    · intro k hk
      rw [hsame k (by omega)]
      exact hfirst k hk
    · intro _
      rw [hsame (q+1) (by omega)]
      exact hnext

theorem extremal_prefix (n : Nat) :
    ∃ path : Nat → Nat, path 0 = 3*2^n-1 ∧ MatchesPrefix t path (8*2^n-3) ∧
      (∀ k, k ≤ 2^n → path k = 3*2^n-1+k) ∧
      (0 < n → path (2^n+1) = 4*2^n+1) := by
  obtain ⟨path, hz, _, hm, hfirst, hnext⟩ := extremal_path n
  exact ⟨path, hz, fun k hk => by simpa only [Nat.zero_add] using hm k hk, hfirst, hnext⟩

theorem shifted_family_prefix (n a : Nat) (ha : a ≤ 2^n) :
    FiniteEditStability.HasPrefix (PhaseShift.shift t a) (3*2^n-a-1) (8*2^n-a-3) := by
  obtain ⟨path, _, hm, hfirst, _⟩ := extremal_prefix n
  have hp := Nat.two_pow_pos n
  have hcut := PhaseShift.suffix_subtraction t path (8*2^n-3) a hm (by omega)
  refine ⟨PhaseShift.subtractSuffix path a, ?_, ?_⟩
  · simp only [PhaseShift.subtractSuffix, Nat.zero_add, hfirst a ha]
    omega
  · have he : 8*2^n-3-a = 8*2^n-a-3 := by omega
    simpa only [he] using hcut

/-- The shifted left endpoint is an exact maximum whenever at most q leading
one-steps are removed. -/
theorem shifted_equality_family (n a : Nat) (ha : a ≤ 2^n) :
    FiniteEditStability.IsMaximumPrefix (PhaseShift.shift t a)
      (3*2^n-a-1) (8*2^n-a-3) ∧
      3*(8*2^n-a-3) = 8*(3*2^n-a-1)+5*a-1 := by
  have hp := Nat.two_pow_pos n
  have heq : 3*(8*2^n-a-3) = 8*(3*2^n-a-1)+5*a-1 := by omega
  refine ⟨⟨shifted_family_prefix n a ha, ?_⟩, heq⟩
  intro len hlen
  obtain ⟨path, hz, hm⟩ := hlen
  have h := PhaseShift.thueMorse_shift_prefix_bound a path len (by omega) hm
  rw [hz] at h
  omega

/-- Geometry alone bounds every displacement between two times of a finite part. -/
theorem part_lower_between (phase len : Nat) (path : Nat → Nat) (h : Part phase path len)
    (i j : Nat) (hij : i ≤ j) (hj : j ≤ len) : path i+(j-i) ≤ path j := by
  induction j with
  | zero =>
    have hi : i = 0 := by omega
    simp [hi]
  | succ j ih =>
    by_cases hi : i ≤ j
    · have hp := ih hi (by omega)
      have he := FiniteEditStability.edge_displacement t (path j) (path (j+1))
        (t (phase+j)) (h j (by omega))
      omega
    · have hi' : i = j+1 := by omega
      simp [hi']

theorem initial_ones_of_minimum_displacement (path : Nat → Nat) (len a : Nat)
    (hm : MatchesPrefix t path len) (ha : a ≤ len) (hend : path a = path 0+a) :
    ∀ k, k ≤ a → path k = path 0+k := by
  have hpart : Part 0 path len := fun k hk => by simpa only [Nat.zero_add] using hm k hk
  intro k hk
  have hlo := part_lower_between 0 len path hpart 0 k (by omega) (by omega)
  have hhi := part_lower_between 0 len path hpart k a hk ha
  omega

/-- The label at a destination determines its unique actual incoming parent. -/
theorem incoming_unique (s : Nat → Bool) (u v w : Nat) (b : Bool)
    (hu : BinaryAvoidance.Edge s u w b) (hv : BinaryAvoidance.Edge s v w b) : u = v := by
  rcases hu.2 with ⟨hu, hbu⟩ | ⟨hu, hbu⟩ <;>
    rcases hv.2 with ⟨hv, hbv⟩ | ⟨hv, hbv⟩
  · omega
  · have hc := hbu.symm.trans hbv
    cases hr : row s w <;> simp only [hr, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, Bool.true_eq_false] at hc
  · have hc := hbu.symm.trans hbv
    cases hr : row s w <;> simp only [hr, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, Bool.true_eq_false] at hc
  · omega

theorem prefix_unique_of_endpoint (s : Nat → Bool) (front back : Nat → Nat)
    (len : Nat) (hf : MatchesPrefix s front len) (hb : MatchesPrefix s back len)
    (hend : front len = back len) : ∀ k, k ≤ len → front k = back k := by
  induction len with
  | zero =>
    intro k hk
    have he : k = 0 := by omega
    simpa only [he] using hend
  | succ len ih =>
    have heq : front len = back len := by
      apply incoming_unique s (front len) (back len) (front (len+1)) (s len)
        (hf len (by omega))
      rw [hend]
      exact hb len (by omega)
    have hearlier := ih (fun k hk => hf k (by omega)) (fun k hk => hb k (by omega)) heq
    intro k hk
    by_cases hsmall : k ≤ len
    · exact hearlier k hsmall
    · have he : k = len+1 := by omega
      simpa only [he] using hend

theorem extremal_terminal (n : Nat) (path : Nat → Nat)
    (hz : path 0 = 3*2^n-1) (hm : MatchesPrefix t path (8*2^n-3)) :
    path (8*2^n-3) = 16*2^n-6 := by
  have hp := Nat.two_pow_pos n
  have hr := SharpThueMorse.binary_prefix_reachable path (8*2^n-3) hm
  rw [hz] at hr
  have hf := (SamuelAlexanderResearch.ThueMorseBound.reachable_iff_interval t t
    (3*2^n-1) (by omega) (8*2^n-3) (path (8*2^n-3))).1 hr
  change SharpThueMorse.X (3*2^n-1) (8*2^n-3) ≤ path (8*2^n-3) ∧
    path (8*2^n-3) < SharpThueMorse.X ((3*2^n-1)+1) (8*2^n-3) at hf
  have hs : (3*2^n-1)+1 = 3*2^n := by omega
  have hright := (SharpThueMorse.common_descent n (3*2^n) (SharpThueMorse.lower_join n)).1
  rw [hs, SharpThueMorse.lower_preterminal n, hright] at hf
  omega

/-- The singleton terminal frontier and unique incoming labels determine the
entire maximal path, up to and including its final vertex. -/
theorem extremal_prefix_unique (n : Nat) (front back : Nat → Nat)
    (hfzero : front 0 = 3*2^n-1) (hbzero : back 0 = 3*2^n-1)
    (hf : MatchesPrefix t front (8*2^n-3)) (hb : MatchesPrefix t back (8*2^n-3)) :
    ∀ k, k ≤ 8*2^n-3 → front k = back k := by
  apply prefix_unique_of_endpoint t front back (8*2^n-3) hf hb
  rw [extremal_terminal n front hfzero hf, extremal_terminal n back hbzero hb]

theorem original_equality_dyadic (path : Nat → Nat) (len : Nat)
    (hv : 1 ≤ path 0) (hm : MatchesPrefix t path len) (heq : 3*len = 8*path 0-1) :
    ∃ n, path 0 = 3*2^n-1 ∧ len = 8*2^n-3 := by
  have hmax : SamuelAlexanderResearch.ThueMorseBound.IsMaximumLength t t (path 0) len := by
    refine ⟨⟨path len, SharpThueMorse.binary_prefix_reachable path len hm⟩, ?_⟩
    intro hnext
    have h := SharpThueMorse.sharp_path_bound (path 0) (len+1) hv hnext
    omega
  exact (SharpThueMorse.sharp_equality_indices (path 0) len hv hmax).1 heq

/-- Equality forces the prepend operation to use only one-step edges. The
unique dyadic extremal path allows that initial run only through time q. -/
theorem shifted_equality_necessary (a : Nat) (path : Nat → Nat) (len : Nat)
    (hv : 1 ≤ path 0) (hm : MatchesPrefix (PhaseShift.shift t a) path len)
    (heq : 3*len = 8*path 0+5*a-1) :
    ∃ n, a ≤ 2^n ∧ path 0 = 3*2^n-a-1 ∧ len = 8*2^n-a-3 := by
  obtain ⟨extended, hlo, hhi, hmatch, hsuffix⟩ :=
    PhaseShift.prepend_shifted_prefix t a path len hm
  have hb := SharpThueMorse.binary_path_prefix_bound extended (len+a) (by omega) hmatch
  have hstart : extended 0 = path 0+a := by omega
  have hext : 3*(len+a) = 8*extended 0-1 := by omega
  obtain ⟨n, hdyadic, hlength⟩ := original_equality_dyadic extended (len+a) (by omega) hmatch hext
  have hp := Nat.two_pow_pos n
  have hjoin := hsuffix 0
  simp only [Nat.zero_add] at hjoin
  have hones := initial_ones_of_minimum_displacement extended (len+a) a hmatch
    (by omega) (by omega)
  have ha : a ≤ 2^n := by
    by_cases ha : a ≤ 2^n
    · exact ha
    · by_cases hn : n = 0
      · subst n
        simp only [Nat.pow_zero] at hdyadic
        omega
      · obtain ⟨extremal, hz, hmext, _, hnext⟩ := extremal_prefix n
        have hmextended : MatchesPrefix t extended (8*2^n-3) := by
          rw [← hlength]
          exact hmatch
        have hsame := extremal_prefix_unique n extended extremal hdyadic hz hmextended hmext
          (2^n+1) (by omega)
        have hfirst := hones (2^n+1) (by omega)
        have htwo := hnext (by omega)
        omega
  exact ⟨n, ha, by omega, by omega⟩

theorem shifted_maximum_exists (a v : Nat) (hv : 1 ≤ v) :
    ∃ len, FiniteEditStability.IsMaximumPrefix (PhaseShift.shift t a) v len ∧
      3*len ≤ 8*v+5*a-1 := by
  have hall : ∀ len, FiniteEditStability.HasPrefix (PhaseShift.shift t a) v len →
      3*len ≤ 8*v+5*a-1 := by
    intro len h
    obtain ⟨path, hz, hm⟩ := h
    have hb := PhaseShift.thueMorse_shift_prefix_bound a path len (by omega) hm
    simpa only [hz] using hb
  obtain ⟨len, hmax⟩ := FiniteEditStability.bounded_prefix_maximum (PhaseShift.shift t a) v
    (8*v+5*a) (fun len h => by have := hall len h; omega)
  exact ⟨len, hmax, hall len hmax.1⟩

/-- Full equality classification for positive-start maxima in the actual graph
built from the shifted Thue--Morse target. -/
theorem shifted_extremal_iff (a v len : Nat) (hv : 1 ≤ v) :
    (FiniteEditStability.IsMaximumPrefix (PhaseShift.shift t a) v len ∧
      3*len = 8*v+5*a-1) ↔
      ∃ n, a ≤ 2^n ∧ v = 3*2^n-a-1 ∧ len = 8*2^n-a-3 := by
  constructor
  · rintro ⟨hmax, heq⟩
    obtain ⟨path, hz, hm⟩ := hmax.1
    have h := shifted_equality_necessary a path len (by omega) hm (by simpa only [hz] using heq)
    simpa only [hz] using h
  · rintro ⟨n, ha, hvn, hlen⟩
    subst v
    subst len
    exact shifted_equality_family n a ha

#print axioms staircase
#print axioms head_path
#print axioms extremal_path
#print axioms shifted_equality_family
#print axioms incoming_unique
#print axioms extremal_prefix_unique
#print axioms shifted_equality_necessary
#print axioms shifted_maximum_exists
#print axioms shifted_extremal_iff

end PhaseExtremal
