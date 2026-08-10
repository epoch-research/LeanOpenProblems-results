import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
example : xi_3 = 0 := by
  simp [xi_3]
example : IsAlgebraic ℚ xi_3 := by
  simp [xi_3]
example : ¬ IsAlgebraic ℚ xi_3 := by
  simp [xi_3]
