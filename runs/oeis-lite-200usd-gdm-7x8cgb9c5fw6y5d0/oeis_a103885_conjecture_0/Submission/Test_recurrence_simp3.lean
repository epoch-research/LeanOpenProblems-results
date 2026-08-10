import FormalConjectures.Util.ProblemImports

open Nat Finset Polynomial

noncomputable def P_witness_gen (m : ℕ) : Polynomial ℝ := (X - C (1/2 : ℝ))^(2 * m)
noncomputable def Q_witness_gen (m : ℕ) : Polynomial ℝ := X^(2 * m)

lemma degree_Q (m : ℕ) : (Q_witness_gen m).degree = (2 * m : ℕ) := by
  unfold Q_witness_gen
  exact degree_X_pow (2 * m)
