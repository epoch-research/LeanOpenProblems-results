import Mathlib

open Polynomial

theorem h_not : ¬ Irreducible (C (2:ℚ) * X + 1) := by
  intro h
  -- can we find a factorization?
  -- C 2 * X + 1 = 2 * (X + 1/2)
  have hfac : C (2:ℚ) * X + 1 = C (2:ℚ) * (X + C (1/2:ℚ)) := by ring
  -- is C 2 a unit?
  have hu : IsUnit (C (2:ℚ)) := by
    -- yes, C 2 is a unit
    sorry
  sorry
