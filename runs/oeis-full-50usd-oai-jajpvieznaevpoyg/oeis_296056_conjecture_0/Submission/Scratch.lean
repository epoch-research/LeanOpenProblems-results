import FormalConjectures.Util.ProblemImports

open Matrix Nat
#check Nat.succ_mul_catalan_eq_centralBinom
#check Nat.catalan_eq_centralBinom_div
#check Matrix.det_mul
#check Matrix.det_smul
#check Matrix.det_mul_column
#check Matrix.det_mul_row
#check Matrix.det_diagonal
#check Matrix.det_vandermonde
#check Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
#check Rat.coe_int_num_of_den_eq_one
#check Rat.den_eq_one_iff
#check Matrix.det_apply
#check Matrix.det_eq_prod_diagonal_of_upperTriangular
#check Matrix.det_of_upperTriangular
#check Matrix.det_zero_of_column_eq_zero
#check Matrix.det_updateColumn_add
#check Matrix.det_updateColumn_smul
#check Matrix.det_updateColumn_self

open Matrix Nat

noncomputable def catbert_matrix2 (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => 1 / (catalan (i.val + j.val) : ℚ)

noncomputable def A2960562 (n : ℕ) : ℚ :=
  if n = 0 then 1
  else (catbert_matrix2 n).det⁻¹

example (n : ℕ) : A2960562 n ∈ Set.range (Int.cast : ℤ → ℚ) := by
  simp [A2960562, catbert_matrix2]
