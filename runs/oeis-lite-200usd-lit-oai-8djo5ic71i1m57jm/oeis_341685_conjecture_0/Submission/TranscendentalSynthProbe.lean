import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
#synth Algebra.Transcendental ℚ (Padic 3)
example : Transcendental ℚ xi_3 := by exact?
example : ¬ IsAlgebraic ℚ xi_3 := by
  exact (show Transcendental ℚ xi_3 from by exact?).not_isAlgebraic
