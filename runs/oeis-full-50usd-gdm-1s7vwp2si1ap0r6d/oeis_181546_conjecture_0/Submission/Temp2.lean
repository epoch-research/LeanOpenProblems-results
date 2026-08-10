import FormalConjectures.Util.ProblemImports

open Filter Asymptotics Real

def F (n L : ℕ) : ℕ :=
  Finset.sum (Finset.range (n / 2 + 1)) fun k => ((n-k).choose k) ^ L

noncomputable def limit_value (L : ℕ) : ℝ :=
  let fib_L : ℝ := Nat.fib L
  let lucas_L : ℝ := (lucasNumber L : ℤ)
  (fib_L * sqrt 5 + lucas_L) / 2

theorem F_zero_eq (n : ℕ) : F n 0 = n / 2 + 1 := by
  simp [F]
