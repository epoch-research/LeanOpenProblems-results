import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
open Algebra
#check DenseRange
#check Rat.denseRange_cast
#check Padic.denseRange_ratCast
#check Padic.denseRange_algebraMap
#check denseRange_iff_closure_range
#check Subalgebra.algebraicClosure
#check mem_algebraicClosure_iff
#check IsClosed
#check isClosed_setOf_isAlgebraic
#check Algebraic.countable
#check Set.Countable.exists_not_mem
example : DenseRange (algebraMap ℚ (Padic 3)) := by
  apply?
example : xi_3 ∈ closure (Set.range (algebraMap ℚ (Padic 3))) := by
  apply?
example : IsAlgebraic ℚ xi_3 := by
  -- if algebraic closure closed and contains dense rationals, this would work, but it should not be closed.
  apply?
