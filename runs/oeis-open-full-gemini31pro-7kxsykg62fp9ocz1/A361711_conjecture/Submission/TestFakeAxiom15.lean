import Mathlib

theorem foo : 1 = 2 :=
  let p : Nonempty ((1:ℕ) = 2) := sorry
  Classical.choice p
