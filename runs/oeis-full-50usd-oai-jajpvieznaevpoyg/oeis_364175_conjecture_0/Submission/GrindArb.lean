import FormalConjectures.Util.ProblemImports
example (f : ℕ → ℕ) (p n r : ℕ) (hp : p.Prime) (h_prime_ge_five : 5 ≤ p)
  (hn : 0 < n) (hr : 0 < r) :
  f (n * p ^ r) ≡ f (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  grind [Nat.ModEq]
