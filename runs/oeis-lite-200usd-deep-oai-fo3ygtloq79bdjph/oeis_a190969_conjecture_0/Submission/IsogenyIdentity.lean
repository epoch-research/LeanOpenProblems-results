import FormalConjectures.Util.ProblemImports

open Polynomial

open scoped Polynomial

noncomputable section

/-- The cubic `y^2 = x^3 - 35x + 98` with CM discriminant `-7`. -/
def fCM : ℤ[X] := X ^ 3 - C 35 * X + C 98

/-- The `-7`-quadratic twist / 7-isogenous curve `y^2 = x^3 - 1715x - 33614`. -/
def gCM : ℤ[X] := X ^ 3 - C 1715 * X - C 33614

/-- Denominator cubic for the explicit 7-isogeny. -/
def DCM : ℤ[X] := X ^ 3 - C 7 * X ^ 2 - C 21 * X + C 91

/-- Numerator polynomial for the `x`-coordinate of the explicit 7-isogeny. -/
def NCM : ℤ[X] :=
  X ^ 7 - C 14 * X ^ 6 + C 343 * X ^ 5 + C 588 * X ^ 4 -
    C 24353 * X ^ 3 + C 120050 * X ^ 2 - C 285719 * X + C 422576

/-- Cleared-denominator identity for the normalized 7-isogeny
`(x,y) ↦ (NCM/DCM^2, y * (NCM/DCM^2)')` from `fCM` to `gCM`.
This is an ordinary polynomial identity over `ℤ`; it is the certificate behind the inert
CM/Hasse-vanishing route. -/
lemma seven_isogeny_cleared_identity :
    fCM * (derivative NCM * DCM - C 2 * NCM * derivative DCM) ^ 2 =
      NCM ^ 3 - C 1715 * NCM * DCM ^ 4 - C 33614 * DCM ^ 6 := by
  simp [fCM, DCM, NCM, derivative_sub, derivative_add, derivative_mul, derivative_pow, derivative_X]
  ring_nf

end

lemma natDegree_fCM : fCM.natDegree = 3 := by
  rw [fCM]
  compute_degree!

/-- The codomain cubic is the `-7`-quadratic twist of `fCM`, expressed using
`Polynomial.scaleRoots`. -/
lemma gCM_eq_scaleRoots : gCM = fCM.scaleRoots (-7 : ℤ) := by
  ext i
  rw [coeff_scaleRoots, natDegree_fCM]
  simp only [gCM, fCM, coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C]
  split_ifs <;> subst_vars <;> norm_num at *

/-- Concrete coefficient effect of the `-7` twist: the Hasse coefficient of `gCM^n`
at degree `2*n` is `(-7)^n` times that of `fCM^n`. -/
lemma coeff_gCM_pow_eq_twist (n : ℕ) :
    (gCM ^ n).coeff (2 * n) = (fCM ^ n).coeff (2 * n) * (-7 : ℤ) ^ n := by
  rw [gCM_eq_scaleRoots]
  rw [← pow_scaleRoots_of_isReduced]
  rw [coeff_scaleRoots]
  rw [natDegree_pow, natDegree_fCM]
  have h : n * 3 - 2 * n = n := by omega
  rw [h]

