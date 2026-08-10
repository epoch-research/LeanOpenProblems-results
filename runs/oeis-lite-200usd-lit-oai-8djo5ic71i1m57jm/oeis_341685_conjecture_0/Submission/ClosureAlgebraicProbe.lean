import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
open Algebra

#check Padic.denseRange_ratCast
#check Algebraic.countable
#check Set.Countable.isClosed
#check Set.Countable.closure
#check isAlgebraic_algebraMap
#check Algebraic.infinite_of_charZero

example : xi_3 ∈ closure {x : Padic 3 | IsAlgebraic ℚ x} := by
  apply DenseRange.closure_eq ?_
  abort
