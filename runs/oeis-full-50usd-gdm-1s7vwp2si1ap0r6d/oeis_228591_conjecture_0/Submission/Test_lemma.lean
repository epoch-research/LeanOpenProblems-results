import FormalConjectures.Util.ProblemImports

open Matrix

theorem det_ne_zero_of_left_mul_eq_smul {n : Type*} [DecidableEq n] [Fintype n] [Nonempty n]
    {R : Type*} [CommRing R] [IsDomain R]
    (A B : Matrix n n R) (d : R) (hd : d ≠ 0) (h : B * A = d • 1) : A.det ≠ 0 := by
  intro h_det
  have h_det_mul : (B * A).det = (d • (1 : Matrix n n R)).det := by rw [h]
  rw [det_mul, h_det, mul_zero] at h_det_mul
  rw [det_smul, det_one, mul_one] at h_det_mul
  have h_pow : d ^ Fintype.card n = 0 := h_det_mul.symm
  have hd_zero : d = 0 := eq_zero_of_pow_eq_zero h_pow
  exact hd hd_zero
