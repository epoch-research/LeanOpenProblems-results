import FormalConjectures.Util.ProblemImports
open BigOperators Finset Nat Real

def omega_mult (k : ℕ) : ℕ := k.factorization.sum (fun _ e => e)
noncomputable def b (n : ℕ) : ℝ :=
  Finset.sum (Icc 1 n) fun k =>
    let sign : ℤ := (fun k : ℕ =>
      let exponent : ℤ := (k : ℤ) - (omega_mult k : ℤ)
      if exponent % 2 = 0 then 1 else -1) k
    (sign : ℝ) / (k : ℝ)

example : (0 > 0 → b 0 < 0) ∧
  (0 > 1 → b 0 < -1 / sqrt (0 : ℝ)) ∧
  (0 > 2008 → b 0 > -log (log (0 : ℝ)) / sqrt (0 : ℝ)) := by simp
