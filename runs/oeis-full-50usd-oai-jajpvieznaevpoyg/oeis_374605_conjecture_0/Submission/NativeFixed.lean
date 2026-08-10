import FormalConjectures.Util.ProblemImports

def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) * (Nat.choose (3 * n + 2 * k) n)

def pp (n : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range ((3*n-1)/2+1)).filter (fun p => decide (n < p ∧ Nat.Prime p)), p^3

example : ∀ n : ℕ, pp n ∣ a n := by
  native_decide
