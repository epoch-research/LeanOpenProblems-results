import Mathlib

theorem foo : False := by
  let rec f : False := f
  exact f
