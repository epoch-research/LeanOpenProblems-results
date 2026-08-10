import FormalConjectures.Util.ProblemImports

open Matrix Nat

lemma det_inv_eq_cast_det {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (B : Matrix (Fin n) (Fin n) ℤ)
    (h : A * (B.map (Int.cast : ℤ → ℚ)) = 1) : A.det⁻¹ = ((B.det : ℤ) : ℚ) := by
  have hdet : A.det * (B.map (Int.cast : ℤ → ℚ)).det = 1 := by
    rw [← det_mul, h, det_one]
  have hdet2 : (B.map (Int.cast : ℤ → ℚ)).det = ((B.det : ℤ) : ℚ) := by
    exact (RingHom.map_det (Int.castRingHom ℚ) B).symm
  rw [hdet2] at hdet
  have h_ne : A.det ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hdet
    norm_num at hdet
  have h_inv : A.det⁻¹ * (A.det * ((B.det : ℤ) : ℚ)) = A.det⁻¹ * 1 := by
    rw [hdet]
  rw [← mul_assoc, inv_mul_cancel₀ h_ne, one_mul, mul_one] at h_inv
  exact h_inv.symm
