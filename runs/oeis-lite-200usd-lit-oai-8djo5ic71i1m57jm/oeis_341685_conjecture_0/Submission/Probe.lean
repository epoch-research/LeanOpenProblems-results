import FormalConjectures.Util.ProblemImports

open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
open Algebra

#check IsAlgebraic
#print IsAlgebraic
#check isAlgebraic_zero
#check isAlgebraic_algebraMap
#check Algebra.IsAlgebraic
#check Algebra.IsAlgebraic.countable
#check Padic.norm
#synth T2Space (Padic 3)
#synth CompleteSpace (Padic 3)
#synth NormedField (Padic 3)
#check Summable
#check HasSum
#check tsum_eq_zero_of_not_summable
#check tsum_eq_zero_of_not_summable

example : ¬ IsAlgebraic ℚ (xi_3) := by
  dsimp [IsAlgebraic]
  simp?

example : IsAlgebraic ℚ (xi_3) := by
  apply?
