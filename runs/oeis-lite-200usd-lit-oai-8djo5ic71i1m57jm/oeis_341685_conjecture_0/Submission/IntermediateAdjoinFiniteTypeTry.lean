import FormalConjectures.Util.ProblemImports
open Nat BigOperators Algebra
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
noncomputable abbrev Kxi := IntermediateField.adjoin ℚ ({xi_3} : Set (Padic 3))

#synth Field Kxi
#synth Algebra ℚ Kxi
#synth Algebra.FiniteType ℚ Kxi
#synth Module.Finite ℚ Kxi
#check IntermediateField.fg_adjoin_finset
#check IntermediateField.fg_adjoin_singleton
#check IntermediateField.adjoin.fg
#check Algebra.IsAlgebraic.of_finiteType_field
#check Algebra.IsAlgebraic.of_finiteType
#check Algebra.IsAlgebraic.of_isField_of_finiteType
#check finite_of_finite_type_of_isField
#check finite_of_finite_type_of_isJacobsonRing
#check IsAlgebraic.of_finiteType
#check IntermediateField.isAlgebraic_adjoin_iff_bot

example : Algebra.IsAlgebraic ℚ Kxi := by
  have hft : Algebra.FiniteType ℚ Kxi := inferInstance
  exact Algebra.IsAlgebraic.of_finiteType_field ℚ Kxi

example : IsAlgebraic ℚ xi_3 := by
  have hK : Algebra.IsAlgebraic ℚ Kxi := by
    have hft : Algebra.FiniteType ℚ Kxi := inferInstance
    exact Algebra.IsAlgebraic.of_finiteType_field ℚ Kxi
  exact hK.isAlgebraic ⟨xi_3, IntermediateField.subset_adjoin (by simp)⟩
