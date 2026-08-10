import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
open Algebra

example : False := by
  simp

example : False := by
  aesop

example : False := by
  grind

example : ¬ IsAlgebraic ℚ xi_3 := by
  grind

example : IsAlgebraic ℚ xi_3 := by
  grind
