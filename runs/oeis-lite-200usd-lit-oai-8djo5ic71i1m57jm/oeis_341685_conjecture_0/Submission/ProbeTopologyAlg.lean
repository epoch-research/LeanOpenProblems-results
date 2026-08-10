import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := by constructor; norm_num
open Algebra
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))

#check Algebraic.countable (R := ℚ) (A := Padic 3)
#check Set.Countable
#check Set.Countable.exists_not_mem
#check Set.Countable.exists_not_mem_of_infinite
#check Padic.denseRange_ratCast (p := 3)
#check DenseRange.exists_nhds
#check IsClosed.mem_of_tendsto
#check isClosed_setOf_isAlgebraic
#check Algebra.IsAlgebraic.cardinalMk_le_max (R := ℚ) (A := Padic 3)
#check Algebraic.cardinalMk_le_max (R := ℚ) (A := Padic 3)
