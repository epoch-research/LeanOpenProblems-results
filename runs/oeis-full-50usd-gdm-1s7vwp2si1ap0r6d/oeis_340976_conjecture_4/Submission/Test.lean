import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  let sigma1_n : ℕ := n.divisors.sum id
  (Ioo 1 n).sum fun k : ℕ => sigma1_n % k

theorem oeis_340976_conjecture_4 :
  ∀ L : ℕ, L ≥ 2 → ∃ N : ℕ, ∀ i : ℕ, i < L → a (N + i) % 2 = 1 := by
  answer(sorry)





