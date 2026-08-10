import FormalConjectures.Util.ProblemImports

open Nat Finset Polynomial

noncomputable def P_witness_gen (m : ℕ) : Polynomial ℝ := (X * (1 - X))^m
noncomputable def Q_witness_gen (m : ℕ) : Polynomial ℝ := (X * (X - 1))^m

lemma degree_P (m : ℕ) : (P_witness_gen m).degree = (2 * m : ℕ) := by
  unfold P_witness_gen
  sorry
