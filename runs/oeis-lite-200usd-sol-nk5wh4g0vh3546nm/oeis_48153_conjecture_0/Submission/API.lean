import FormalConjectures.Util.ProblemImports

#check ZMod.LFunction_def_odd
#check ZMod.LFunction
#check HurwitzZeta.hurwitzZetaOdd_apply_zero
#check HurwitzZeta.hurwitzZeta_apply_zero
#check DirichletCharacter.IsPrimitive.completedLFunction_one_sub
#check DirichletCharacter.LFunction_eq_completed_div_gammaFactor
#check DirichletCharacter.LFunction_ne_zero_of_one_le_re
#check LSeries.tendsto_atTop
#check DirichletCharacter.LFunction_eq_LSeries
#check DirichletCharacter.Odd.gammaFactor_def
#check Gammaℝ_one
#check Gammaℝ_two
#check Complex.cpow_natCast
#check ZMod.val

example : Complex.Gammaℝ (2 : ℂ) = (Real.pi : ℂ)⁻¹ := by
  rw [Complex.Gammaℝ_def]
  rw [show (2 : ℂ) / 2 = 1 by norm_num, Complex.Gamma_one]
  rw [show -(2 : ℂ) / 2 = -1 by norm_num, Complex.cpow_neg_one]
