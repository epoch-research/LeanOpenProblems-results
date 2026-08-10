import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := by constructor; norm_num
#check Padic.eq_ratNorm
#check Padic.norm_rat_le_one
#check Padic.valuation_ratCast
#check Rat.padicValuation_self
#check Rat.AbsoluteValue.padic_eq_padicNorm

example : False := by
  have h := Padic.eq_ratNorm (p := 3) (q := (3:ℚ))
  -- whatever type
  guard_target = False
  sorry
