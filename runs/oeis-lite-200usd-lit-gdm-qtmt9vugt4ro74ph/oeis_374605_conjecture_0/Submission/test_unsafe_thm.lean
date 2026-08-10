import Mathlib.Data.Nat.Choose.Basic

def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) * (Nat.choose (3 * n + 2 * k) n)

unsafe def oeis_374605_conjecture_0_unsafe (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (n : ℕ) (hn1 : (2 * p + 3) / 3 ≤ n) (hn2 : n ≤ p - 1) :
    (p ^ 3 : ℕ) ∣ a n :=
  oeis_374605_conjecture_0_unsafe p hp hp5 n hn1 hn2

theorem oeis_374605_conjecture_0 (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
  ∀ n : ℕ,
    (2 * p + 3) / 3 ≤ n →
    n ≤ p - 1 →
    (p ^ 3 : ℕ) ∣ a n := by
  intro n hn1 hn2
  exact oeis_374605_conjecture_0_unsafe p hp hp5 n hn1 hn2
