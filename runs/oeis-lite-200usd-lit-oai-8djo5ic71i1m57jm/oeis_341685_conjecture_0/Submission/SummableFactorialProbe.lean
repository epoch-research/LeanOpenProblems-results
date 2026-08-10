import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num

example : Summable (fun k : ℕ => (Nat.factorial k : Padic 3)) := by
  exact?

example : ¬ Summable (fun k : ℕ => (Nat.factorial k : Padic 3)) := by
  exact?

example : Tendsto (fun k : ℕ => (Nat.factorial k : Padic 3)) atTop (𝓝 0) := by
  exact?
