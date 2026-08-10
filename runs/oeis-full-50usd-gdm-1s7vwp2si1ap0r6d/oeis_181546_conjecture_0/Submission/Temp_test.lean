import FormalConjectures.Util.ProblemImports

open Filter Asymptotics Real

def F (n L : ℕ) : ℕ :=
  Finset.sum (Finset.range (n / 2 + 1)) fun k => ((n-k).choose k) ^ L

noncomputable def limit_value (L : ℕ) : ℝ :=
  let fib_L : ℝ := Nat.fib L
  let lucas_L : ℝ := (lucasNumber L : ℤ)
  (fib_L * sqrt 5 + lucas_L) / 2

theorem oeis_181546_conjecture_0 (L : ℕ) :
    Tendsto (fun n => (F (n+1) L : ℝ) / (F n L : ℝ)) atTop (nhds (limit_value L)) := answer(sorry)
