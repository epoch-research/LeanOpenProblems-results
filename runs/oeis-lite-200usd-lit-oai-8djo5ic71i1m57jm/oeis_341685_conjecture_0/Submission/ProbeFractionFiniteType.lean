import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := by constructor; norm_num
open Algebra
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))

noncomputable abbrev Kx := Algebra.adjoin ℚ ({xi_3} : Set (Padic 3))

#synth IsDomain Kx
#synth Algebra.FiniteType ℚ Kx
#synth Algebra.FiniteType ℚ (FractionRing Kx)
#synth Algebra ℚ (FractionRing Kx)
#synth IsScalarTower ℚ Kx (FractionRing Kx)
#check IsFractionRing.injective (A := Kx) (K := FractionRing Kx)
#check Algebra.FiniteType.localization
#check Algebra.FiniteType.of_isLocalization
#check Algebra.FiniteType.of_isLocalization_finite
#check IsLocalization.FiniteType
#check IsLocalization.finiteType
#check Algebra.IsAlgebraic.of_finiteType_field
#check Algebra.IsAlgebraic.of_finiteType
#check Algebra.isAlgebraic_of_finiteType
#check IsAlgebraic.of_finiteType
#check zariski_lemma
#check Zariski

example : Algebra.FiniteType ℚ Kx := by
  -- maybe prove by FG iff
  rw [← Subalgebra.fg_iff_finiteType]
  exact Subalgebra.fg_adjoin_singleton xi_3

example : Algebra.FiniteType ℚ (FractionRing Kx) := by
  infer_instance
