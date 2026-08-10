import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))

example : IsIntegral ℚ xi_3 := by
  unfold IsIntegral
  guard_target = xi_3 ∈ integralClosure ℚ (Padic 3)
  apply?
