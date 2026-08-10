import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset

def a (n : ℕ) : ℕ :=
  let A018804_n : ℕ := (Finset.Ico 1 (n + 1)).sum fun k => Nat.gcd k n
  n / Nat.gcd n (1 + A018804_n)

example : a 1 = 1 := by
  simp [a]

example {p : ℕ} (hp : Nat.Prime p) : a p = 1 := by
  rw [a]
  have hsum : (∑ k ∈ Finset.Ico 1 (p + 1), Nat.gcd k p) = 2 * p - 1 := by
    rw [Finset.sum_eq_card_nsmul]
    sorry
  sorry
