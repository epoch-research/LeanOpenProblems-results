import Mathlib

open Polynomial

theorem not_irred_0 : ¬ Irreducible (0 : Polynomial ℚ) := by
  exact not_irreducible_zero
