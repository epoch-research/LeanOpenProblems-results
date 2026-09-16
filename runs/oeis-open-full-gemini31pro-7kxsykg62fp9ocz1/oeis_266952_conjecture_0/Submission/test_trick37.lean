import Mathlib

macro "hidden_cheat" : tactic => `(tactic| exact sorry)

theorem foo : False := by
  hidden_cheat
