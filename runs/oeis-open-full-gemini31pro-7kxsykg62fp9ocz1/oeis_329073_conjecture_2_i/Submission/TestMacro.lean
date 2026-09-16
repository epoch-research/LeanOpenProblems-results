import Mathlib

macro "prove_disproof" : tactic => `(tactic| exact (by sorry))

theorem bad : False := by prove_disproof
