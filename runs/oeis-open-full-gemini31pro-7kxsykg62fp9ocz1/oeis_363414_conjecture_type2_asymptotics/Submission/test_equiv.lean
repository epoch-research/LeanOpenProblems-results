import Mathlib

open Filter Asymptotics

theorem not_equiv : ¬ (fun n : ℕ ↦ (n : ℝ) + 1) ~[atTop] (fun n : ℕ ↦ (n : ℝ)) := by
  sorry
