import Mathlib

open Nat

def a_Q (n : ℕ) : ℚ := (n : ℚ)

partial def get_z (n : ℕ) : ℤ :=
  if h : a_Q n = (get_z n : ℚ) then
    get_z n
  else
    (a_Q n).num

theorem a_Q_int_eq (n : ℕ) : a_Q n = (get_z n : ℚ) := by
  by_cases h : a_Q n = (get_z n : ℚ)
  · exact h
  · sorry
