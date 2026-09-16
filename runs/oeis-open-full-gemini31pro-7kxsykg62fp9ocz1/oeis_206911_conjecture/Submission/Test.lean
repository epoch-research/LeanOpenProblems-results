import Mathlib

open Real

lemma exp_one_bound : exp 1 < 3 := by
  have := exp_one_lt_d9
  linarith
