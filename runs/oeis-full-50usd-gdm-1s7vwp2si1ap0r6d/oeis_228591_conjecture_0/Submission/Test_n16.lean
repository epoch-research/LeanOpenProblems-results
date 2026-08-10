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

def M_16 : Matrix (Fin 16) (Fin 16) ℤ :=
  fun (i j : Fin 16) =>
    let k := i.val + j.val + 2
    if k = 2 ∨ (k % 2 = 1 ∧ ¬ k.Prime) then (1 : ℤ) else (0 : ℤ)

def B_16 : Matrix (Fin 16) (Fin 16) ℤ :=
  !![0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0; -1, -1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1; 0, 0, 2, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0; 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0; 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1; 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0; 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0; 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0; 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]

theorem B_16_mul_M_16 : B_16 * M_16 = (1 : ℤ) • (1 : Matrix (Fin 16) (Fin 16) ℤ) := by
  decide

theorem M_16_det_ne_zero : M_16.det ≠ 0 := by
  apply det_ne_zero_of_left_mul_eq_smul M_16 B_16 (1 : ℤ) (by decide) B_16_mul_M_16
