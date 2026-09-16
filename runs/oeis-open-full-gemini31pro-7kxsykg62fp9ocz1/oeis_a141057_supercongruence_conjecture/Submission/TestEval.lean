import FormalConjectures.Util.ProblemImports

open Nat Finset

def A141057 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun n₁ =>
    Finset.sum (Finset.range (n - n₁ + 1)) fun n₂ =>
      (choose n n₁ * choose (n - n₁) n₂) ^ 3

#eval (A141057 (1 * 7 ^ 1) : ℤ) ≡ A141057 (1 * 7 ^ 0) [ZMOD (7 ^ (3 * 1))]
