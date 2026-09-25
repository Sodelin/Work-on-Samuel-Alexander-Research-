import SamuelAlexanderResearch.QuantitativeAvoidance

/-!
Arbitrarily slow finite-path extinction for a constructed aperiodic word.
Finite words are represented by an executable length and bit function.
The next word repeats the previous word, appends an equally long zero block,
and ends with one true bit. Bits outside a word's length are immaterial.
-/

namespace SlowAvoidance

open BinaryAvoidance QuantitativeAvoidance

def wordLength (f : Nat → Nat) : Nat → Nat
  | 0 => 1
  | j + 1 => 2 * ((f (2 * wordLength f j - 1) + 2) * wordLength f j) + 1

def start (f : Nat → Nat) (j : Nat) : Nat := 2 * wordLength f j - 1

def blockLength (f : Nat → Nat) (j : Nat) : Nat :=
  (f (start f j) + 2) * wordLength f j

def matchLength (f : Nat → Nat) (j : Nat) : Nat :=
  (f (start f j) + 1) * wordLength f j

def wordBit (f : Nat → Nat) : Nat → Nat → Bool
  | 0, k => decide (k = 0)
  | j + 1, k =>
      if k < blockLength f j then wordBit f j (k % wordLength f j)
      else if k < 2 * blockLength f j then false
      else decide (k = 2 * blockLength f j)

def target (f : Nat → Nat) (k : Nat) : Bool := wordBit f (k + 1) k

theorem wordLength_succ (f : Nat → Nat) (j : Nat) :
    wordLength f (j + 1) = 2 * blockLength f j + 1 := rfl

theorem wordLength_pos (f : Nat → Nat) (j : Nat) : 0 < wordLength f j := by
  cases j <;> simp only [wordLength] <;> omega

theorem wordLength_le_blockLength (f : Nat → Nat) (j : Nat) :
    wordLength f j ≤ blockLength f j := by
  exact Nat.le_mul_of_pos_left _ (by omega)

theorem wordLength_grows (f : Nat → Nat) (j : Nat) :
    wordLength f j < wordLength f (j + 1) := by
  have := wordLength_le_blockLength f j
  rw [wordLength_succ]
  omega

theorem stage_le_wordLength (f : Nat → Nat) (j : Nat) : j + 1 ≤ wordLength f j := by
  induction j with
  | zero => simp [wordLength]
  | succ j ih => have := wordLength_grows f j; omega

theorem wordLength_mono (f : Nat → Nat) (j k : Nat) (h : j ≤ k) :
    wordLength f j ≤ wordLength f k := by
  induction k with
  | zero =>
    have : j = 0 := by omega
    subst j
    exact Nat.le_refl _
  | succ k ih =>
    by_cases hj : j ≤ k
    · have := ih hj
      have := wordLength_grows f k
      omega
    · have : j = k + 1 := by omega
      subst j
      exact Nat.le_refl _

theorem wordBit_extends (f : Nat → Nat) (j k : Nat) (hk : k < wordLength f j) :
    wordBit f (j + 1) k = wordBit f j k := by
  have hblock : k < blockLength f j := Nat.lt_of_lt_of_le hk (wordLength_le_blockLength f j)
  simp only [wordBit, if_pos hblock, Nat.mod_eq_of_lt hk]

theorem wordBit_coherent (f : Nat → Nat) (j l k : Nat) (hjl : j ≤ l)
    (hk : k < wordLength f j) : wordBit f l k = wordBit f j k := by
  induction l with
  | zero =>
    have : j = 0 := by omega
    subst j
    rfl
  | succ l ih =>
    by_cases hj : j ≤ l
    · have hkl : k < wordLength f l := Nat.lt_of_lt_of_le hk (wordLength_mono f j l hj)
      rw [wordBit_extends f l k hkl]
      exact ih hj
    · have : j = l + 1 := by omega
      subst j
      rfl

theorem target_agrees (f : Nat → Nat) (j k : Nat) (hk : k < wordLength f j) :
    target f k = wordBit f j k := by
  dsimp [target]
  by_cases h : j ≤ k + 1
  · exact wordBit_coherent f j (k + 1) k h hk
  · have hsmall : k < wordLength f (k + 1) := by have := stage_le_wordLength f (k+1); omega
    exact (wordBit_coherent f (k+1) j k (by omega) hsmall).symm

theorem blockLength_split (f : Nat → Nat) (j : Nat) :
    blockLength f j = matchLength f j + wordLength f j := by
  simp only [blockLength, matchLength, Nat.add_mul, Nat.one_mul, Nat.two_mul]
  omega

theorem matchLength_exceeds (f : Nat → Nat) (j : Nat) :
    f (start f j) < matchLength f j := by
  have := Nat.le_mul_of_pos_right (f (start f j) + 1) (wordLength_pos f j)
  dsimp [matchLength]
  omega

theorem target_periodic_prefix (f : Nat → Nat) (j k : Nat)
    (hk : k < matchLength f j) :
    target f (k + wordLength f j) = target f k := by
  have hsplit := blockLength_split f j
  have hp := wordLength_pos f j
  have hleft : k < blockLength f j := by omega
  have hright : k + wordLength f j < blockLength f j := by omega
  have hlen := wordLength_succ f j
  rw [target_agrees f (j+1) (k + wordLength f j) (by omega),
      target_agrees f (j+1) k (by omega)]
  simp only [wordBit, if_pos hleft, if_pos hright, Nat.add_mod_right]

theorem target_zero_block (f : Nat → Nat) (j k : Nat)
    (hlow : blockLength f j ≤ k) (hhigh : k < 2 * blockLength f j) :
    target f k = false := by
  rw [target_agrees f (j+1) k (by rw [wordLength_succ]; omega)]
  simp only [wordBit, if_neg (by omega : ¬ k < blockLength f j), if_pos hhigh]

theorem target_terminal_true (f : Nat → Nat) (j : Nat) :
    target f (2 * blockLength f j) = true := by
  have hp := wordLength_pos f j
  have hb := wordLength_le_blockLength f j
  rw [target_agrees f (j+1) (2 * blockLength f j) (by rw [wordLength_succ]; omega)]
  simp only [wordBit, if_neg (by omega : ¬ 2 * blockLength f j < blockLength f j),
    Nat.lt_irrefl, if_false, decide_true]

theorem target_aperiodic (f : Nat → Nat) : ¬ EventuallyPeriodic (target f) := by
  rintro ⟨N, p, hp, period⟩
  let j := N + p
  let M := blockLength f j
  have hb : j + 1 ≤ M := Nat.le_trans (stage_le_wordLength f j) (wordLength_le_blockLength f j)
  have hzero : target f (2*M-p) = false := target_zero_block f j _ (by dsimp [j, M] at *; omega) (by omega)
  have htrue : target f (2*M) = true := target_terminal_true f j
  have hperiod := period (2*M-p) (by dsimp [j] at *; omega)
  have heq : 2*M-p+p = 2*M := by dsimp [j] at *; omega
  rw [heq, hzero, htrue] at hperiod
  contradiction

theorem starts_strict (f : Nat → Nat) (i j : Nat) (hij : i < j) :
    start f i < start f j := by
  have h1 := wordLength_grows f i
  have h2 := wordLength_mono f (i+1) j (by omega)
  have hp := wordLength_pos f i
  dsimp [start]
  omega

theorem finite_match_exceeds (f : Nat → Nat) (j : Nat) :
    ∃ path : Nat → Nat, path 0 = start f j ∧
      MatchesPrefix (target f) path (matchLength f j) ∧
      f (start f j) < matchLength f j := by
  obtain ⟨path, hstart, hmatch⟩ := periodic_prefix_gives_match (target f)
    (wordLength f j) (matchLength f j) (wordLength_pos f j)
    (fun k hk => target_periodic_prefix f j k hk)
  exact ⟨path, hstart, hmatch, matchLength_exceeds f j⟩

theorem no_infinite_match (f : Nat → Nat) : ¬ ∃ path, Matches (target f) path :=
  aperiodic_target_avoided (target f) (target_aperiodic f)

/-- Arbitrarily slow extinction along strictly increasing starting vertices. -/
theorem arbitrarily_slow_avoidance (f : Nat → Nat) :
    ∃ s : Nat → Bool, ¬ EventuallyPeriodic s ∧
      (¬ ∃ path, Matches s path) ∧
      ∃ starts : Nat → Nat,
        (∀ i j, i < j → starts i < starts j) ∧
        ∀ j, ∃ len, f (starts j) < len ∧
          ∃ path : Nat → Nat, path 0 = starts j ∧ MatchesPrefix s path len := by
  refine ⟨target f, target_aperiodic f, no_infinite_match f, start f,
    starts_strict f, ?_⟩
  intro j
  obtain ⟨path, hstart, hmatch, hlong⟩ := finite_match_exceeds f j
  exact ⟨matchLength f j, hlong, path, hstart, hmatch⟩

#print axioms target_agrees
#print axioms target_periodic_prefix
#print axioms target_aperiodic
#print axioms starts_strict
#print axioms finite_match_exceeds
#print axioms no_infinite_match
#print axioms arbitrarily_slow_avoidance

end SlowAvoidance
