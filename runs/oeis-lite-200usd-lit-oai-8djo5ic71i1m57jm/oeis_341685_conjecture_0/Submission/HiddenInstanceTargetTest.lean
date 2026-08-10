import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))

#print IsAlgebraic

noncomputable def stdAlg : Algebra ℚ (Padic 3) := inferInstance

example : IsAlgebraic ℚ xi_3 := by
  letI : Algebra ℚ (Padic 3) := stdAlg
  change @IsAlgebraic ℚ (Padic 3) _ _ stdAlg xi_3
  sorry

-- Try a different algebra via aeval 0? not an Algebra ℚ maybe all unique
#synth Subsingleton (Algebra ℚ (Padic 3))
