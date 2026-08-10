import FormalConjectures.Util.ProblemImports

def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) * (Nat.choose (3 * n + 2 * k) n)

set_option maxHeartbeats 200000
example (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (n : ℕ)
    (h1 : (2 * p + 3) / 3 ≤ n) (h2 : n ≤ p - 1) : (p ^ 3 : ℕ) ∣ a n := by
  exact?
