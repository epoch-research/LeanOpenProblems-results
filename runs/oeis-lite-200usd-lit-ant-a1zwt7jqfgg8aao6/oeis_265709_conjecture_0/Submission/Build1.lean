import FormalConjectures.Util.ProblemImports
open Nat Finset ArithmeticFunction

noncomputable def f : ArithmeticFunction ℚ where
  toFun := fun n => if n = 0 then 0 else (1 : ℚ) / ((sigma 1) n : ℚ)
  map_zero' := by simp

-- the sum equals (zeta * f) n
example (n : ℕ) : (↑ζ * f) n = ∑ d ∈ n.divisors, f d := coe_zeta_mul_apply

-- f is multiplicative
example : f.IsMultiplicative := by
  constructor
  · simp [f]
  · intro m n hmn
    simp only [f]
    sorry
