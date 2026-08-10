import Submission.CatEntry

open Matrix Nat Finset

noncomputable def catbert_matrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => 1 / (catalan (i.val + j.val) : ℚ)

noncomputable def H (n : ℕ) (a b : ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => poch a (i.val + j.val) / poch b (i.val + j.val)

lemma catbert_eq_scaled_H (n : ℕ) :
    catbert_matrix n = Matrix.of (fun i j : Fin n => ((4:ℚ)^i.val)⁻¹ * ((4:ℚ)^j.val)⁻¹ * H n 2 (1/2) i j) := by
  ext i j
  simp [catbert_matrix, H]
  rw [catalan_inv_poch (i.val+j.val)]
  rw [pow_add]
  field_simp
  ring

lemma det_catbert_scaled (n : ℕ) :
    (catbert_matrix n).det = (((4:ℚ) ^ (∑ i : Fin n, i.val))⁻¹)^2 * (H n 2 (1/2)).det := by
  classical
  rw [catbert_eq_scaled_H]
  let v : Fin n → ℚ := fun i => ((4:ℚ)^i.val)⁻¹
  let M : Matrix (Fin n) (Fin n) ℚ := H n 2 (1/2)
  have hscale : (Matrix.of fun i j : Fin n => v i * v j * M i j).det = (∏ i, v i) * (∏ j, v j) * M.det := by
    calc
      (Matrix.of fun i j : Fin n => v i * v j * M i j).det
          = (Matrix.of fun i j : Fin n => v i * (Matrix.of fun i j : Fin n => v j * M i j) i j).det := by
            congr; ext i j; simp; ring
      _ = (∏ i, v i) * (Matrix.of fun i j : Fin n => v j * M i j).det := by rw [Matrix.det_mul_column]
      _ = (∏ i, v i) * ((∏ j, v j) * M.det) := by rw [Matrix.det_mul_row]
      _ = (∏ i, v i) * (∏ j, v j) * M.det := by ring
  rw [hscale]
  have hprod : (∏ i : Fin n, v i) = ((4:ℚ) ^ (∑ i : Fin n, i.val))⁻¹ := by
    simp [v, Finset.prod_inv_distrib, ← Finset.prod_pow_eq_pow_sum]
  rw [hprod]
  ring
