import FormalConjectures.Util.ProblemImports
open Nat BigOperators Polynomial
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
#check Padic.summable_factorial
#check Padic.hasSum_factorial
#check tsum_eq_zero
#check tsum_eq_zero_of_not_summable
#check tsum_congr
#check Padic.tendsto_pow_factorial_nhds_zero
#check Padic.hasSum
#check Padic.summable
#reduce xi_3
example : xi_3 = 0 := by
  simp [xi_3]
example : IsAlgebraic ℚ xi_3 := by
  rw [show xi_3 = 0 by simp [xi_3]]
  exact isAlgebraic_zero
