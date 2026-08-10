import FormalConjectures.Util.ProblemImports
example (p n r : ℕ) (hp : p.Prime) (h_prime_ge_five : 5 ≤ p)
    (hn : 0 < n) (hr : 0 < r) : n * p ^ r = n * p ^ (r - 1) := by
  nlinarith [h_prime_ge_five, hn, hr]
