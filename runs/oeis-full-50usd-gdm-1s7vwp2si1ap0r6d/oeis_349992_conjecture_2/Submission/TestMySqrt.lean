import FormalConjectures.Util.ProblemImports

def my_sqrt_fuel (n : ℕ) : ℕ → ℕ → ℕ
  | 0, k => k
  | fuel + 1, k =>
    if (k + 1) * (k + 1) ≤ n then
      my_sqrt_fuel n fuel (k + 1)
    else
      k

def my_sqrt (n : ℕ) : ℕ :=
  my_sqrt_fuel n n 0

theorem test_my_sqrt : my_sqrt 2 = 1 := by rfl

