import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := by constructor; norm_num
open Algebra
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
#print IsAlgebraic
#print Algebra.IsAlgebraic
#reduce IsAlgebraic ℚ (xi_3)
#check (show IsAlgebraic ℚ (0 : Padic 3) by exact isAlgebraic_zero)
#check (show IsAlgebraic ℚ (1 : Padic 3) by exact isAlgebraic_one)
