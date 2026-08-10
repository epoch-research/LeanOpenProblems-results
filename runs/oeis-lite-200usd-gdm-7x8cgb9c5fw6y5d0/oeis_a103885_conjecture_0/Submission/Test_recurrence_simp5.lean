import FormalConjectures.Util.ProblemImports

open Nat Finset Polynomial

noncomputable def P_witness_gen (m : ℕ) : Polynomial ℝ := (X - C (1/2 : ℝ))^(2 * m)

lemma degree_P (m : ℕ) : (P_witness_gen m).degree = (2 * m : ℕ) := by
  unfold P_witness_gen
  have h1 : (X - C (1/2 : ℝ)).degree = 1 := by
    rw [degree_sub_eq_left_of_degree_lt]
    · exact degree_X
    · rw [degree_X]
      have : (C (1/2 : ℝ)).degree ≤ 0 := degree_C_le
      exact lt_of_le_of_lt this (by decide)
  rw [degree_pow, h1]
  simp
