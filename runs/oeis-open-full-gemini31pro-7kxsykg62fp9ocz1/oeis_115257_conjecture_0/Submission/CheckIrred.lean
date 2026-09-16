import Mathlib

open Polynomial

theorem poly_fake_irred : Irreducible (X : Polynomial ℚ) := by
  apply irreducible_of_degree_eq_one
  exact degree_X

#print poly_fake_irred
