import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num

example : Summable (fun k : ℕ => (Nat.factorial k : Padic 3)) := by
  infer_instance

example : ¬ Summable (fun k : ℕ => (Nat.factorial k : Padic 3)) := by
  intro h
  -- no
  fail_if_success exact h.not_tendsto_zero ?_
  sorry
