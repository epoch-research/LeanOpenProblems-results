import FormalConjectures.Util.ProblemImports
#check Nat.squarefreePart_of_isSquare
#check Nat.squarefreePart_mul_squarePart
#print axioms Nat.squarefreePart_of_isSquare
example : False := by
  have h0 : IsSquare (0:ℕ) := ⟨0, by norm_num⟩
  have h := Nat.squarefreePart_of_isSquare h0
  norm_num at h
