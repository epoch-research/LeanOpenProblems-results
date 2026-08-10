import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3_local : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
#check Algebra.finite_adjoin
#check Algebra.adjoin.fg
#check Algebra.adjoin_fg
#check Algebra.FiniteType.of_adjoin_eq_top
#check Algebra.FiniteType.adjoin
#check Algebra.adjoin_singleton_eq_range_aeval
#check isAlgebraic_adjoin_iff
#check isAlgebraic_adjoin_simple
#check Algebra.IsAlgebraic.of_finite
#check IsAlgebraic.of_finite

example : Algebra.FiniteType ℚ (Algebra.adjoin ℚ ({xi_3_local} : Set (Padic 3))) := by
  infer_instance

example : Module.Finite ℚ (Algebra.adjoin ℚ ({xi_3_local} : Set (Padic 3))) := by
  infer_instance
