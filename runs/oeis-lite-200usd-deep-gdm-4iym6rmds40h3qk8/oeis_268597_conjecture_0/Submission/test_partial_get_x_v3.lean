import Mathlib

open Nat Classical

noncomputable partial def get_x (n : ℕ) : ℕ :=
  if h : ∃ x > 0, (x - 1) % Nat.totient x = n then
    Classical.choose h
  else
    1
