import Mathlib

open ArithmeticFunction

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

lemma no_sol_0_50 : ∀ x < 50, x ≠ 0 → (sigma 1 x) % x ≠ 5 := by decide

lemma no_sol_50_100 : ∀ x < 100, x ≥ 50 → x ≠ 0 → (sigma 1 x) % x ≠ 5 := by decide

lemma no_sol_100_150 : ∀ x < 150, x ≥ 100 → x ≠ 0 → (sigma 1 x) % x ≠ 5 := by decide
