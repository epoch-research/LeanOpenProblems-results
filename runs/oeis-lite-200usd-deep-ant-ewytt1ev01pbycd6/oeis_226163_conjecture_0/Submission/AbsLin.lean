import FormalConjectures.Util.ProblemImports

open Matrix

/-- Key sub-lemma: an orthogonal matrix with determinant `1` over odd dimension
has `1 - O` singular. -/
theorem orthogonal_odd_det_one_sub {m : ℕ} (hm : Odd m)
    (O : Matrix (Fin m) (Fin m) ℚ)
    (horth : Oᵀ * O = 1) (hdet : O.det = 1) :
    (1 - O).det = 0 := by
  have hOOt : O * Oᵀ = 1 := mul_eq_one_comm.2 horth
  -- (O - 1).det = (1 - O).det
  have h1 : (O - 1).det = (1 - O).det := by
    have step : O - 1 = O * (1 - Oᵀ) := by
      rw [Matrix.mul_sub, Matrix.mul_one, hOOt]
    rw [step, Matrix.det_mul, hdet, one_mul]
    have : (1 - Oᵀ) = (1 - O)ᵀ := by
      rw [Matrix.transpose_sub, Matrix.transpose_one]
    rw [this, Matrix.det_transpose]
  -- (O - 1).det = - (1 - O).det
  have h2 : (O - 1).det = - (1 - O).det := by
    have : O - 1 = -(1 - O) := (neg_sub 1 O).symm
    rw [this, Matrix.det_neg, Fintype.card_fin, hm.neg_one_pow, neg_one_mul]
  -- combine
  linarith [h1, h2]

theorem abstract_singular {m : ℕ} (hm : Odd m)
    (S Z : Matrix (Fin m) (Fin m) ℚ)
    (hnorm : S * Sᵀ = Sᵀ * S) (hS : IsUnit S.det)
    (hZsym : Zᵀ = Z) (hZ2 : Z * Z = 1) (hZdet : Z.det = 1) :
    (S - Sᵀ * Z).det = 0 := by
  set O : Matrix (Fin m) (Fin m) ℚ := S⁻¹ * Sᵀ * Z with hO
  -- S * O = Sᵀ * Z
  have hSO : S * O = Sᵀ * Z := by
    rw [hO, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv S hS, Matrix.one_mul]
  -- O is orthogonal
  have horth : Oᵀ * O = 1 := by
    have hSinv : IsUnit (Sᵀ).det := by rwa [Matrix.det_transpose]
    -- Oᵀ = Z * S * (Sᵀ)⁻¹
    have hOt : Oᵀ = Z * S * (Sᵀ)⁻¹ := by
      rw [hO]
      rw [Matrix.transpose_mul, Matrix.transpose_mul, hZsym]
      rw [Matrix.transpose_nonsing_inv, Matrix.transpose_transpose]
      rw [Matrix.mul_assoc]
    rw [hOt, hO]
    -- (Sᵀ)⁻¹ * S⁻¹ = S⁻¹ * (Sᵀ)⁻¹
    have hcomm : (Sᵀ)⁻¹ * S⁻¹ = S⁻¹ * (Sᵀ)⁻¹ := by
      have e1 : (S * Sᵀ)⁻¹ = (Sᵀ * S)⁻¹ := by rw [hnorm]
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev] at e1
      exact e1
    calc Z * S * (Sᵀ)⁻¹ * (S⁻¹ * Sᵀ * Z)
        = Z * S * ((Sᵀ)⁻¹ * S⁻¹) * Sᵀ * Z := by
          simp only [Matrix.mul_assoc]
      _ = Z * S * (S⁻¹ * (Sᵀ)⁻¹) * Sᵀ * Z := by rw [hcomm]
      _ = Z * (S * S⁻¹) * ((Sᵀ)⁻¹ * Sᵀ) * Z := by
          simp only [Matrix.mul_assoc]
      _ = Z * 1 * 1 * Z := by
          rw [Matrix.mul_nonsing_inv S hS, Matrix.nonsing_inv_mul Sᵀ hSinv]
      _ = Z * Z := by rw [Matrix.mul_one, Matrix.mul_one]
      _ = 1 := hZ2
  -- O.det = 1
  have hOdet : O.det = 1 := by
    rw [hO, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hZdet, mul_one]
    have : (S⁻¹).det * S.det = 1 := by
      rw [← Matrix.det_mul, Matrix.nonsing_inv_mul S hS, Matrix.det_one]
    rw [this]
  -- apply sub-lemma
  have hkey : (1 - O).det = 0 := orthogonal_odd_det_one_sub hm O horth hOdet
  -- S - Sᵀ*Z = S * (1 - O)
  have hfact : S - Sᵀ * Z = S * (1 - O) := by
    rw [Matrix.mul_sub, Matrix.mul_one, hSO]
  rw [hfact, Matrix.det_mul, hkey, mul_zero]

#print axioms abstract_singular
