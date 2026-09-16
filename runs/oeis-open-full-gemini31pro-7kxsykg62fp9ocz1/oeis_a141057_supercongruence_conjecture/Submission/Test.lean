import FormalConjectures.Util.ProblemImports

def A141057 (n : ℕ) : ℕ := 0

#check ∀ (p k n : ℕ), (A141057 (n * p ^ k) : ℤ) ≡ A141057 (n * p ^ (k - 1)) [ZMOD (p ^ (3 * k))]
