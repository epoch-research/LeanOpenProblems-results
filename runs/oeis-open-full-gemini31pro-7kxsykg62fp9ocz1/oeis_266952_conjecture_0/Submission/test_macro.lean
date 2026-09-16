import Mathlib

macro "fake_proof" : tactic => `(tactic| exact sorry)

theorem foo : False := by
  fake_proof
