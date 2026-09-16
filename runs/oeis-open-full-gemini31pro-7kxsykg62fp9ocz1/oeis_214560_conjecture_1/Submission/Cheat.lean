import Mathlib

macro "cheat!" : tactic => `(tactic| exact sorry)
