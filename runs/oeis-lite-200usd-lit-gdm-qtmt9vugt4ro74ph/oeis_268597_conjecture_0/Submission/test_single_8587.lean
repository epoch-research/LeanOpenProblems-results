import Mathlib

set_option maxRecDepth 200000

open Nat

theorem test_8587 : 8587 > 0 ∧ (8587 - 1) % Nat.totient 8587 = 306 := by
  decide
