import FormalConjectures.Util.ProblemImports

#synth IsField ℤ
#synth DenselyOrdered ℤ
#synth DenselyOrdered (WithZero (Multiplicative ℤ))
#synth FirstCountableTopology (OnePoint ℚ)
#synth SecondCountableTopology (OnePoint ℚ)
#synth IsSolvable (Equiv.Perm (Fin 5))
#check Int.not_isField
#check Int.not_denselyOrdered
#check not_denselyOrdered_withZero_int
#check Rat.not_firstCountableTopology_opc
#check Rat.not_secondCountableTopology_opc
#check Equiv.Perm.fin_5_not_solvable

example : False := by exact Int.not_isField (inferInstance)
example : False := by exact Int.not_denselyOrdered (inferInstance)
example : False := by exact not_denselyOrdered_withZero_int (inferInstance)
example : False := by exact Rat.not_firstCountableTopology_opc (inferInstance)
example : False := by exact Rat.not_secondCountableTopology_opc (inferInstance)
example : False := by exact Equiv.Perm.fin_5_not_solvable (inferInstance)
