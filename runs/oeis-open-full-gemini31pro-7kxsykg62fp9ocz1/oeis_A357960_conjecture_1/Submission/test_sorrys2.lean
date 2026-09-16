import Submission.Spec
open Nat

theorem oeis_A357960_conjecture_1.disproof2 : ¬ (type_of% @oeis_A357960_conjecture_1) := by
  intro h
  have hp : Nat.Prime 3 := by decide
  have h3 : 3 ≤ 3 := by decide
  have h_false : a 3 ≡ a 1 [MOD 3^5] := h 3 hp h3
  revert h_false
  sorry

