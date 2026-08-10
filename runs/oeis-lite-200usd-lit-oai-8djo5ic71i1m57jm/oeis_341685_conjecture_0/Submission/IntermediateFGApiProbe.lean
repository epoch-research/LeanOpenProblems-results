import FormalConjectures.Util.ProblemImports
open Nat BigOperators Algebra
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
noncomputable abbrev Kxi := IntermediateField.adjoin ℚ ({xi_3} : Set (Padic 3))
#check (IntermediateField.fg_adjoin_finset ({xi_3} : Finset (Padic 3)))
#check IntermediateField.FG
#check IntermediateField.FG.finiteDimensional
#check IntermediateField.FG.finiteType
#check IntermediateField.FG.essFiniteType
#check IntermediateField.essFiniteType_iff
#check IntermediateField.finiteDimensional_adjoin
#check IntermediateField.adjoin.finiteDimensional
#check IntermediateField.adjoin.finiteDimensional'
#check IntermediateField.adjoin.finiteDimensional_finset
