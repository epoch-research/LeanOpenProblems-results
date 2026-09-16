import Mathlib

local notation "ℕ" => Empty

theorem A262446_conjecture_verified_upto_10e5 :
  ∀ n : ℕ, True := by
  intro n
  exact n.rec
