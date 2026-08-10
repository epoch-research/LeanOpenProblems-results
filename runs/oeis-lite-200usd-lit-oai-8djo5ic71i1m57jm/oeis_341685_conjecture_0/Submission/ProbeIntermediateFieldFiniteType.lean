import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := by constructor; norm_num
open Algebra
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
noncomputable abbrev IFx := IntermediateField.adjoin ℚ ({xi_3} : Set (Padic 3))

#synth Field IFx
#synth Algebra ℚ IFx
#synth Algebra.FiniteType ℚ IFx
#synth Module.Finite ℚ IFx
#synth FiniteDimensional ℚ IFx
#check IntermediateField.fg_adjoin_finset
#check IntermediateField.fg_adjoin_of_finite
#check IntermediateField.FG
#check finite_of_finite_type_of_isJacobsonRing ℚ IFx

example : Algebra.FiniteType ℚ IFx := by
  infer_instance

example : Module.Finite ℚ IFx := by
  exact finite_of_finite_type_of_isJacobsonRing ℚ IFx

example : IsAlgebraic ℚ xi_3 := by
  have hxmem : xi_3 ∈ (IFx : Set (Padic 3)) := by
    exact IntermediateField.subset_adjoin (show xi_3 ∈ ({xi_3} : Set (Padic 3)) by simp)
  let y : IFx := ⟨xi_3, hxmem⟩
  have hy : IsAlgebraic ℚ y := by exact IsAlgebraic.of_finite ℚ y
  -- map subtype to padic
  exact hy.algHom (IntermediateField.val (IntermediateField.adjoin ℚ ({xi_3} : Set (Padic 3))))
