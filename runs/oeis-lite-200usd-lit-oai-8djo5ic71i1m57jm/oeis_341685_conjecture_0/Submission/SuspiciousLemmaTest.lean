import FormalConjectures.Util.ProblemImports

-- Test nthRoot lemmas at concrete negative/even values.
example : nthRoot 2 (-1 : ℝ) = (-1 : ℝ) ^ ((2 : ℕ)⁻¹ : ℝ) := by
  simpa using nthRoot_of_even (n:=2) (by decide : Even 2) (-1 : ℝ)
#eval (Float.sqrt (-1.0))
#check Real.rpow
#check Real.rpow_of_neg
#check Real.rpow_neg

example : nthRoot 2 ((-1 : ℝ)^2) = (-1 : ℝ) := by
  have h : ((2 : ℕ) ≠ 0 ∧ 0 ≤ ((-1 : ℝ)^2)) ∨ Odd 2 := by left; constructor <;> norm_num
  simpa using nthRoot_pow (n:=2) (-1 : ℝ) h

example : False := by
  have h1 : nthRoot 2 ((-1 : ℝ)^2) = (-1 : ℝ) := by
    have h : ((2 : ℕ) ≠ 0 ∧ 0 ≤ ((-1 : ℝ)^2)) ∨ Odd 2 := by left; constructor <;> norm_num
    simpa using nthRoot_pow (n:=2) (-1 : ℝ) h
  have h2 : nthRoot 2 ((-1 : ℝ)^2) = (1 : ℝ) := by norm_num [nthRoot]
  nlinarith
#print axioms nthRoot_pow
