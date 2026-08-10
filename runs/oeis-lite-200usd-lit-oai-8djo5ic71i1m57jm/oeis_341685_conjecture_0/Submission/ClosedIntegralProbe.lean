import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
#check isClosed_setOf_isIntegral
#check isClosed_setOf_isAlgebraic
#check IsIntegral.isClosed
#check IsAlgebraic.isClosed
#check isClosed_integralClosure
#check isClosed_algebraicClosure
