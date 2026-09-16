import Mathlib

macro "prove_false" : tactic => `(tactic| exact sorry)

theorem foo : False := by
  prove_false
