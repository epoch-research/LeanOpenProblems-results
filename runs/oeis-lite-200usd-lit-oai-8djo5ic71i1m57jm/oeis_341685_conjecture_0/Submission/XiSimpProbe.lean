import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
example : IsAlgebraic ℚ (0 : Padic 3) := by
  exact isAlgebraic_zero
example : xi_3 = 0 := by
  simp [xi_3]
