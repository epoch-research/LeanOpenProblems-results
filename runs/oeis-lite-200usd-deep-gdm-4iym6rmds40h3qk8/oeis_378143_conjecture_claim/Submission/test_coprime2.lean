import Mathlib

open Nat

set_option exponentiation.threshold 100000
set_option maxRecDepth 200000

theorem test_coprime : ¬ 3 ∣ 10 ^ 8192 + 1 := by decide
