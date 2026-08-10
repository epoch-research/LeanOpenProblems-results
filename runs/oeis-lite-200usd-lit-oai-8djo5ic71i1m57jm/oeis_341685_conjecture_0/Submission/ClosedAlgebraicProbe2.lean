import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
open Algebra
#check isClosed_setOf_isAlgebraic
#check Algebraic.isClosed
#check algebraicClosure
#check mem_algebraicClosure_iff
#check Padic.denseRange_ratCast
#check Padic.denseRange_algebraMap
#check DenseRange.closure_range
example : Set.range (algebraMap ℚ (Padic 3)) ⊆ {x : Padic 3 | IsAlgebraic ℚ x} := by
  intro x hx
  rcases hx with ⟨q, rfl⟩
  exact isAlgebraic_algebraMap q
example : IsClosed {x : Padic 3 | IsAlgebraic ℚ x} := by
  exact isClosed_setOf_isAlgebraic ℚ (Padic 3)
