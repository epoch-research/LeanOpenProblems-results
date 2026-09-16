import Mathlib

theorem test (p : ℕ) [Fact p.Prime] (x : Padic p) : ‖x‖ = ‖x‖ := rfl
#check norm_div
#check padicNorm
