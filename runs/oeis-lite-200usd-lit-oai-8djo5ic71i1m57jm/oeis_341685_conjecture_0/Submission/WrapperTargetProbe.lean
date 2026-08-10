import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
#synth Fact (IsAlgebraic ℚ xi_3)
#synth Fact (¬ IsAlgebraic ℚ xi_3)
#synth Nonempty (IsAlgebraic ℚ xi_3)
#synth Nonempty (¬ IsAlgebraic ℚ xi_3)
#synth Inhabited (IsAlgebraic ℚ xi_3)
#synth Inhabited (¬ IsAlgebraic ℚ xi_3)
#synth Erased (IsAlgebraic ℚ xi_3)
