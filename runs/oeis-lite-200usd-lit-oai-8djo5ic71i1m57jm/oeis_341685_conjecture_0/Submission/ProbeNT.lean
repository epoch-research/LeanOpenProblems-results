import FormalConjectures.Util.ProblemImports

open Nat

example : False := by
  -- try deciding contradictory perfect power facts
  have h0 : ¬ Nat.IsPerfectPower 0 := by decide
  have h1 : ¬ Nat.IsPerfectPower 1 := by decide
  have h2 : ¬ Nat.IsPerfectPower 2 := by decide
  -- no contradiction
  fail_if_success exact h0 (by decide : Nat.IsPerfectPower 0)
  fail_if_success exact h1 (by decide : Nat.IsPerfectPower 1)
  fail_if_success exact h2 (by decide : Nat.IsPerfectPower 2)
  sorry
