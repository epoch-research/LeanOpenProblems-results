import FormalConjectures.Util.ProblemImports

def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) * (Nat.choose (3 * n + 2 * k) n)

example : (5^3 : ℕ) ∣ a 4 := by native_decide
example : (7^3 : ℕ) ∣ a 5 := by native_decide
example : (7^3 : ℕ) ∣ a 6 := by native_decide
example : (11^3 : ℕ) ∣ a 8 := by native_decide
