import FormalConjectures.Util.ProblemImports

open Nat Finset Polynomial

noncomputable def P_witness_gen (m : ℕ) : Polynomial ℝ := (X - C (1/2 : ℝ))^(2 * m)

lemma degree_P (m : ℕ) : (P_witness_gen m).degree = (2 * m : ℕ) := by
  unfold P_witness_gen
  have h1 : (X - C (1/2 : ℝ)).degree = 1 := by
    -- let's prove the degree of X - C (1/2) is 1
    rw [degree_sub_eq_left_of_degree_lt]
    · exact degree_X
    · rw [degree_X, degree_C (1/2 : ℝ)]
      exact WithBot.coe_lt_coe.mpr (by decide)
  rw [degree_pow, h1]
  -- now we need to show nsmul 1 (2*m) = 2*m
  simp
