import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := by constructor; norm_num
open Algebra
noncomputable def xi_tmp : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))

#synth Algebra.FiniteType ℚ (Algebra.adjoin ℚ ({xi_tmp} : Set (Padic 3)))
#synth IsDomain (Algebra.adjoin ℚ ({xi_tmp} : Set (Padic 3)))
#synth IsField (Algebra.adjoin ℚ ({xi_tmp} : Set (Padic 3)))
#synth Field (Algebra.adjoin ℚ ({xi_tmp} : Set (Padic 3)))
#check Algebra.IsAlgebraic.of_finiteType_of_isField
#check Algebra.IsAlgebraic.of_finiteType
#check Algebra.IsAlgebraic.of_isField_of_finiteType
#check Algebra.isAlgebraic_of_finiteType_of_isField
#check RingHom.FiniteType.isAlgebraic_of_isField
#check Algebra.FiniteType.isAlgebraic
#check IsIntegralClosure.isAlgebraic
#check Subalgebra.isField

example : IsAlgebraic ℚ xi_tmp := by
  let A := Algebra.adjoin ℚ ({xi_tmp} : Set (Padic 3))
  have hmem : xi_tmp ∈ A := by exact Algebra.subset_adjoin (by simp)
  -- if A algebraic over Q, hmem gives algebraic element
  have hAlg : Algebra.IsAlgebraic ℚ A := by
    apply?
  exact hAlg.isAlgebraic ⟨xi_tmp, hmem⟩ |>.map ?_
