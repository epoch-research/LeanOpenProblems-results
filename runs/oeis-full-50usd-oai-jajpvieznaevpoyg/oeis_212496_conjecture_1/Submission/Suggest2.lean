import FormalConjectures.Util.ProblemImports
open BigOperators Finset Nat Real

def omega_mult (k : ℕ) : ℕ := k.factorization.sum (fun _ e => e)
noncomputable def b (n : ℕ) : ℝ :=
  Finset.sum (Icc 1 n) fun k =>
    let sign : ℤ := (fun k : ℕ =>
      let exponent : ℤ := (k : ℤ) - (omega_mult k : ℤ)
      if exponent % 2 = 0 then 1 else -1) k
    (sign : ℝ) / (k : ℝ)
example (n : ℕ) (hn : n > 0) : b n < 0 := by
  exact?
example (n : ℕ) (hn : n > 1) : b n < -1 / sqrt (n : ℝ) := by
  exact?
example (n : ℕ) (hn : n > 2008) : b n > -log (log (n : ℝ)) / sqrt (n : ℝ) := by
  exact?
