import FormalConjectures.Util.ProblemImports

example : Real.nthRoot 2 (-1 : ℝ) = (-1 : ℝ) ^ ((2 : ℕ)⁻¹ : ℝ) := by
  simpa using Real.nthRoot_of_even (n:=2) (by decide : Even 2) (-1 : ℝ)

-- This should fail: cannot prove the hypothesis for negative r.
example : ¬ (((2 : ℕ) ≠ 0 ∧ 0 ≤ (-1 : ℝ)) ∨ Odd 2) := by norm_num

#check Real.iteratedLog_two
#check Real.iteratedLog_four
#print axioms Real.iteratedLog_two
#print axioms Real.iteratedLog_four

#check Nat.squarefreePart_zero
#check Nat.squarePart_zero
#check Nat.squarefreePart_mul_squarePart
example : (0 : ℕ).squarefreePart * (0 : ℕ).squarePart = 0 := Nat.squarefreePart_mul_squarePart 0
example : (0 : ℕ).squarefreePart = 1 := Nat.squarefreePart_zero
example : (0 : ℕ).squarePart = 0 := Nat.squarePart_zero
