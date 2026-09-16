import Mathlib

open Polynomial

theorem not_irred_q1 : ¬ Irreducible (C (2:ℚ) * X + 1) := by
  intro h
  have heq : C (2:ℚ) * X + 1 = C 2 * (X + C (1/2)) := by ring
  rw [heq] at h
  have hu : IsUnit (C (2:ℚ)) := isUnit_C.mpr (by decide)
  have hX : ¬ IsUnit (X + C (1/2:ℚ)) := by
    intro hX
    have hdeg : degree (X + C (1/2:ℚ)) = 0 := degree_eq_zero_of_isUnit hX
    have hdeg2 : degree (X + C (1/2:ℚ)) = 1 := by
      have hd1 : degree (X : ℚ[X]) = 1 := degree_X
      have hd2 : degree (C (1/2:ℚ)) ≤ 0 := degree_C_le
      rw [degree_add_eq_left_of_degree_lt]
      · exact hd1
      · exact lt_of_le_of_lt hd2 (by decide)
    rw [hdeg2] at hdeg
    revert hdeg; decide
  have himp := h.isUnit_or_isUnit heq
  -- wait, Irreducible means if it's written as a * b, one is a unit.
  -- Here it's written as C 2 * (X + C 1/2) and C 2 is a unit, which is allowed for irreducible elements!
  -- So C 2 * X + 1 IS irreducible!
  sorry
