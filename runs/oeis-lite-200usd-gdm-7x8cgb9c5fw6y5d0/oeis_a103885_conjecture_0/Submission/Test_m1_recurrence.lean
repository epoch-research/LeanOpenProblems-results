import FormalConjectures.Util.ProblemImports

open Nat Finset Polynomial

private def product_indices (m : ℕ) : Finset ℕ :=
  Finset.Ioc 0 (2 * m)

noncomputable def prod_factor_minus (m n : ℕ) : ℝ :=
  (product_indices m).prod fun k =>
    ((2 * m * n : ℝ) - (k : ℝ))

lemma prod_minus_one (n : ℕ) : prod_factor_minus 1 n = (2 * n - 1) * (2 * n - 2) := by
  unfold prod_factor_minus product_indices
  have h_set : Finset.Ioc 0 (2 * 1) = {1, 2} := by decide
  rw [h_set]
  simp
