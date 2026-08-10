import Mathlib

partial def unsound_proof (x : ℕ) : False :=
  unsound_proof (x + 1)

theorem test_unsound : False :=
  unsound_proof 0

