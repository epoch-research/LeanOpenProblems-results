import FormalConjectures.Util.ProblemImports
#check Nat.div_add_mod
#check Nat.mod_add_div
#check Nat.add_div_le_add_div
#check Nat.add_div
#check Nat.div_le_div_right
#check Nat.div_le_div_left
#check Nat.div_le_div
#check Nat.add_mul_div_left
#check Nat.mul_div_right
example (a b c : ℕ) : a / c + b / c ≤ (a + b) / c := by
  by_cases hc : c = 0
  · simp [hc]
  · exact Nat.add_div_le_add_div a b c
