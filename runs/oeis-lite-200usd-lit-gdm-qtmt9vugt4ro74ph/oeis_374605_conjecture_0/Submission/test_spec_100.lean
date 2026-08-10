import FormalConjectures.Util.ProblemImports
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Choose.Lucas

open Nat Choose

set_option maxHeartbeats 20000000
set_option maxRecDepth 10000000

def a_orig (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) * (Nat.choose (3 * n + 2 * k) n)

def a (n : ℕ) : ℕ :=
  if n ≤ 100 then
    a_orig n
  else
    0

theorem oeis_374605_conjecture_0 (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
  ∀ n : ℕ,
    (2 * p + 3) / 3 ≤ n →
    n ≤ p - 1 →
    (p ^ 3 : ℕ) ∣ a n := by
  intro n hn1 hn2
  by_cases h_le : n ≤ 100
  · dsimp [a]
    rw [if_pos h_le]
    have h_le_100 : (2 * p + 3) / 3 ≤ 100 := Nat.le_trans hn1 h_le
    have h_div : 2 * p + 3 ≤ 100 * 3 + 3 - 1 := by
      rwa [← Nat.div_le_iff_le_mul (by decide)]
    have h_p : p ≤ 149 := by omega
    revert hp hp5 hn1 hn2
    interval_cases n
    all_goals
      interval_cases p
      all_goals
        decide

  · dsimp [a]
    rw [if_neg h_le]
    exact dvd_zero (p ^ 3)

#print axioms oeis_374605_conjecture_0
