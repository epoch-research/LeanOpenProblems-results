import Mathlib

set_option maxRecDepth 200000

open Nat

theorem test_385 : 4706 > 0 ∧ (4706 - 1) % Nat.totient 4706 = 385 := by
  decide
