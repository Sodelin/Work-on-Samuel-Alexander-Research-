import SamuelAlexanderResearch.ThueMorseBits

namespace ThueMorseWindow
open ThueMorseBits

def odd (n : Nat) : Bool := n % 2 == 1

theorem odd_succ (n : Nat) : odd (n+1) = !(odd n) := by
  by_cases h : n % 2 = 0
  · have h1 : (n+1) % 2 = 1 := by omega
    simp [odd, h, h1]
  · have h0 : n % 2 = 1 := by omega
    have h1 : (n+1) % 2 = 0 := by omega
    simp [odd, h0, h1]

theorem reflected_window (n r : Nat) (hr : 1 ≤ r) (hbound : r ≤ 2^n) :
    t (2^n-r) = Bool.xor (odd n) (t (r-1)) := by
  induction n generalizing r with
  | zero =>
    have heq : r = 1 := by simpa using Nat.le_antisymm hbound hr
    subst r
    simp [odd]
  | succ n ih =>
    have hpow : 2^(n+1) = 2 * 2^n := by rw [Nat.pow_succ]; omega
    have hpos : 0 < 2^n := Nat.two_pow_pos n
    by_cases hlow : r ≤ 2^n
    · have heq : 2^(n+1)-r = 1*2^n+(2^n-r) := by omega
      rw [heq, t_dyadic_block 1 n (2^n-r) (by omega), ih r hr hlow, odd_succ]
      rw [t_one]
      cases odd n <;> cases t (r-1) <;> rfl
    · let s := r-2^n
      have hs : 1 ≤ s := by dsimp [s]; omega
      have hsb : s ≤ 2^n := by dsimp [s]; omega
      have heq : 2^(n+1)-r = 2^n-s := by dsimp [s]; omega
      have heqr : r-1 = 1*2^n+(s-1) := by dsimp [s]; omega
      rw [heq, ih s hs hsb, heqr, t_dyadic_block 1 n (s-1) (by omega), odd_succ]
      rw [t_one]
      cases odd n <;> cases t (s-1) <;> rfl

theorem left_window (n r : Nat) (hr : 1 ≤ r) (hbound : r ≤ 2^n) :
    t (3*2^n-r) = Bool.xor (!(odd n)) (t (r-1)) := by
  have heq : 3*2^n-r = 2*2^n+(2^n-r) := by omega
  rw [heq, t_dyadic_block 2 n (2^n-r) (by omega), reflected_window n r hr hbound]
  rw [t_two]
  cases odd n <;> cases t (r-1) <;> rfl

theorem right_window (n r : Nat) (hbound : r < 2^n) :
    t (3*2^n+r) = t r := by
  simpa using t_dyadic_block 3 n r hbound

theorem same_parity_left_window (n m r : Nat) (hr : 1 ≤ r)
    (hn : r ≤ 2^n) (hm : r ≤ 2^m) (hp : n%2=m%2) :
    t (3*2^n-r) = t (3*2^m-r) := by
  rw [left_window n r hr hn, left_window m r hr hm]
  simp [odd, hp]

theorem same_right_window (n m r : Nat) (hn : r < 2^n) (hm : r < 2^m) :
    t (3*2^n+r) = t (3*2^m+r) := by
  rw [right_window n r hn, right_window m r hm]

end ThueMorseWindow
#print axioms ThueMorseWindow.reflected_window
#print axioms ThueMorseWindow.same_parity_left_window
#print axioms ThueMorseWindow.same_right_window
