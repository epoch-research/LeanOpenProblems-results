/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fin.Rev

/-!
# The integral Krylov right-inverse certificate for Erdős 975

This file formalizes the algebraic certificate in section 4 of
`/tmp/erdos975_adjoint_orbit_audit.md`. It does not import the specification or
assert the full Erdős conjecture (or any balanced counting asymptotic).

For a commutative ring `R`, a square matrix `A`, and vectors `x, y`, the matrix
`krylovRows r A x` has rows `xᵀ A^k` and `krylovColumns r A y` has columns
`A^j y`. Their product has entry `xᵀ A^(k+j) y`. If the moments before `r - 1`
vanish and the moment at `r - 1` is `-1`, reversing the columns gives a lower
triangular matrix with diagonal `-1`, without imposing any condition on the
higher moments. Its determinant is `(-1)^(r * (r + 1) / 2)`.

The row count is allowed to be general; the application has `d ≥ 2` and
`r = d - 1`. In particular, the certificate is valid over `ℤ` and in every
characteristic, not just over a field.
-/

namespace Erdos975Support

open Matrix

variable {R : Type*} [CommRing R] {d r : ℕ}

/-- The bilinear moment `xᵀ A^k y`, with no transpose convention hidden in `A`. -/
def krylovMoment (A : Matrix (Fin d) (Fin d) R) (x y : Fin d → R) (k : ℕ) : R :=
  dotProduct x ((A ^ k).mulVec y)

/-- The `r × d` matrix whose row `k` is `xᵀ A^k`. -/
def krylovRows (r : ℕ) (A : Matrix (Fin d) (Fin d) R) (x : Fin d → R) :
    Matrix (Fin r) (Fin d) R :=
  fun k i ↦ (vecMul x (A ^ k.val)) i

/-- The `d × r` matrix whose column `j` is `A^j y`. -/
def krylovColumns (r : ℕ) (A : Matrix (Fin d) (Fin d) R) (y : Fin d → R) :
    Matrix (Fin d) (Fin r) R :=
  fun i j ↦ ((A ^ j.val).mulVec y) i

/-- All entries of the square product are moments, including the unrestricted
higher moments. -/
theorem krylovRows_mul_krylovColumns_apply
    (A : Matrix (Fin d) (Fin d) R) (x y : Fin d → R) (k j : Fin r) :
    (krylovRows r A x * krylovColumns r A y) k j =
      krylovMoment A x y (k.val + j.val) := by
  change dotProduct (vecMul x (A ^ k.val)) ((A ^ j.val).mulVec y) = _
  rw [← dotProduct_mulVec, mulVec_mulVec, ← pow_add]
  rfl

/-- Applying the row matrix gives precisely the initial moments. -/
theorem krylovRows_mulVec_apply
    (A : Matrix (Fin d) (Fin d) R) (x y : Fin d → R) (k : Fin r) :
    (krylovRows r A x).mulVec y k = krylovMoment A x y k.val := by
  exact (dotProduct_mulVec x (A ^ k.val) y).symm

private theorem sign_fin_revPerm (r : ℕ) :
    Equiv.Perm.sign (Fin.revPerm (n := r)) = (-1 : ℤˣ) ^ (r * (r - 1) / 2) := by
  rw [Equiv.Perm.sign_eq_prod_prod_Iio]
  have hprod : (∏ j : Fin r, ∏ i ∈ Finset.Iio j,
      (if Fin.revPerm i < Fin.revPerm j then (1 : ℤˣ) else -1)) =
      ∏ j : Fin r, (-1 : ℤˣ) ^ j.val := by
    apply Finset.prod_congr rfl
    intro j _
    calc
      (∏ i ∈ Finset.Iio j, (if Fin.revPerm i < Fin.revPerm j then (1 : ℤˣ) else -1)) =
          ∏ _i ∈ Finset.Iio j, (-1 : ℤˣ) := by
        apply Finset.prod_congr rfl
        intro i hi
        have hij : i < j := Finset.mem_Iio.mp hi
        have hrev : j.rev < i.rev := Fin.rev_lt_rev.mpr hij
        simp only [Fin.revPerm_apply, if_neg (not_lt_of_gt hrev)]
      _ = (-1 : ℤˣ) ^ j.val := by simp [Fin.card_Iio]
  rw [hprod, Finset.prod_pow_eq_pow_sum]
  congr 1
  exact (Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ i) r).trans (Finset.sum_range_id r)

private theorem triangular_exponent (r : ℕ) :
    r * (r - 1) / 2 + r = r * (r + 1) / 2 := by
  calc
    r * (r - 1) / 2 + r = ∑ i ∈ Finset.range (r + 1), i := by
      rw [Finset.sum_range_succ, Finset.sum_range_id]
    _ = r * (r + 1) / 2 := by
      rw [Finset.sum_range_id, Nat.add_sub_cancel, Nat.mul_comm]

/-- Reversing the columns of an anti-triangular matrix gives a lower
triangular matrix. The entries on the other side of the anti-diagonal are
unrestricted. -/
theorem reversedColumns_lowerTriangular_of_antitriangular
    (H : Matrix (Fin r) (Fin r) R)
    (hzero : ∀ i j : Fin r, i.val + j.val < r - 1 → H i j = 0) :
    (H.submatrix id (Fin.revPerm (n := r))).BlockTriangular OrderDual.toDual := by
  intro i j hij
  change i < j at hij
  change H i j.rev = 0
  apply hzero
  have hj := j.isLt
  have hi := i.isLt
  simp only [Fin.val_rev]
  omega

/-- The diagonal after column reversal is the original anti-diagonal. -/
theorem reversedColumns_diagonal_of_antitriangular
    (H : Matrix (Fin r) (Fin r) R)
    (hanti : ∀ i j : Fin r, i.val + j.val = r - 1 → H i j = -1)
    (i : Fin r) :
    H.submatrix id (Fin.revPerm (n := r)) i i = -1 := by
  change H i i.rev = -1
  apply hanti
  have hi := i.isLt
  simp only [Fin.val_rev]
  omega

/-- The exact determinant of an anti-triangular matrix with anti-diagonal
`-1`, over any commutative ring. -/
theorem det_of_antitriangular_neg_one
    (H : Matrix (Fin r) (Fin r) R)
    (hzero : ∀ i j : Fin r, i.val + j.val < r - 1 → H i j = 0)
    (hanti : ∀ i j : Fin r, i.val + j.val = r - 1 → H i j = -1) :
    H.det = (-1 : R) ^ (r * (r + 1) / 2) := by
  let B := H.submatrix id (Fin.revPerm (n := r))
  have hB : B.det = (-1 : R) ^ r := by
    rw [det_of_lowerTriangular B
      (reversedColumns_lowerTriangular_of_antitriangular H hzero)]
    simp only [B, reversedColumns_diagonal_of_antitriangular H hanti]
    simp
  have hrev : B.submatrix id (Fin.revPerm (n := r)) = H := by
    ext i j
    simp [B, Fin.revPerm_apply]
  calc
    H.det = (Equiv.Perm.sign (Fin.revPerm (n := r)) : R) * B.det := by
      rw [← det_permute', hrev]
    _ = (-1 : R) ^ (r * (r - 1) / 2) * (-1 : R) ^ r := by
      rw [hB, sign_fin_revPerm]
      simp
    _ = (-1 : R) ^ (r * (r + 1) / 2) := by
      rw [← pow_add, triangular_exponent]

/-- The determinant certificate is derived from the stated initial moments;
the determinant is not an additional premise. -/
theorem krylov_product_det
    (A : Matrix (Fin d) (Fin d) R) (x y : Fin d → R)
    (hzero : ∀ k : ℕ, k < r - 1 → krylovMoment A x y k = 0)
    (hlast : krylovMoment A x y (r - 1) = -1) :
    (krylovRows r A x * krylovColumns r A y).det =
      (-1 : R) ^ (r * (r + 1) / 2) := by
  apply det_of_antitriangular_neg_one
  · intro i j hij
    rw [krylovRows_mul_krylovColumns_apply]
    exact hzero _ hij
  · intro i j hij
    rw [krylovRows_mul_krylovColumns_apply, hij]
    exact hlast

/-- The determinant in the moment certificate is a unit, even when `R` is
not a field or an integral domain. -/
theorem krylov_product_det_isUnit
    (A : Matrix (Fin d) (Fin d) R) (x y : Fin d → R)
    (hzero : ∀ k : ℕ, k < r - 1 → krylovMoment A x y k = 0)
    (hlast : krylovMoment A x y (r - 1) = -1) :
    IsUnit (krylovRows r A x * krylovColumns r A y).det := by
  rw [krylov_product_det A x y hzero hlast]
  exact IsUnit.pow _ isUnit_neg_one

/-- A unit determinant of a square product gives an explicit RIGHT inverse
of the rectangular first matrix over a commutative ring. No field assumption
or division by a possibly nonunit is used. -/
theorem rightInverse_of_isUnit_det_product
    (M : Matrix (Fin r) (Fin d) R) (C : Matrix (Fin d) (Fin r) R)
    (hdet : IsUnit (M * C).det) :
    M * (C * (M * C)⁻¹) = 1 := by
  rw [← Matrix.mul_assoc]
  exact Matrix.mul_nonsing_inv (M * C) hdet

/-- A matrix right inverse also gives a right inverse of the map on column
vectors. -/
theorem mulVec_rightInverse_of_mul_eq_one
    (M : Matrix (Fin r) (Fin d) R) (B : Matrix (Fin d) (Fin r) R)
    (hMB : M * B = 1) :
    Function.RightInverse B.mulVec M.mulVec := by
  intro v
  rw [mulVec_mulVec, hMB, one_mulVec]

/-- In particular, a rectangular matrix with a right inverse is surjective
on vectors over the ring itself. -/
theorem mulVec_surjective_of_mul_eq_one
    (M : Matrix (Fin r) (Fin d) R) (B : Matrix (Fin d) (Fin r) R)
    (hMB : M * B = 1) :
    Function.Surjective M.mulVec :=
  (mulVec_rightInverse_of_mul_eq_one M B hMB).surjective

/-- The explicit Krylov right-inverse candidate, using the ring-valued
nonsingular inverse of the square product. -/
noncomputable def krylovRightInverse (r : ℕ)
    (A : Matrix (Fin d) (Fin d) R) (x y : Fin d → R) :
    Matrix (Fin d) (Fin r) R :=
  krylovColumns r A y * (krylovRows r A x * krylovColumns r A y)⁻¹

/-- The candidate is a RIGHT inverse under exactly the stated moment
hypotheses, over any commutative ring. -/
theorem krylov_mul_rightInverse
    (A : Matrix (Fin d) (Fin d) R) (x y : Fin d → R)
    (hzero : ∀ k : ℕ, k < r - 1 → krylovMoment A x y k = 0)
    (hlast : krylovMoment A x y (r - 1) = -1) :
    krylovRows r A x * krylovRightInverse r A x y = 1 :=
  rightInverse_of_isUnit_det_product _ _
    (krylov_product_det_isUnit A x y hzero hlast)

/-- Existence of a vector with the special moments forces surjectivity, not
merely full row rank over a fraction field. -/
theorem krylov_surjective_of_moments
    (A : Matrix (Fin d) (Fin d) R) (x y : Fin d → R)
    (hzero : ∀ k : ℕ, k < r - 1 → krylovMoment A x y k = 0)
    (hlast : krylovMoment A x y (r - 1) = -1) :
    Function.Surjective (krylovRows r A x).mulVec :=
  mulVec_surjective_of_mul_eq_one _ _ (krylov_mul_rightInverse A x y hzero hlast)

/-- The special target vector `(0, …, 0, -1)`. For positive `r` its last
coordinate is `-1`; the empty vector is used when `r = 0`. -/
def krylovTarget (r : ℕ) : Fin r → R :=
  fun k ↦ if k.val = r - 1 then -1 else 0

/-- The equation with the special target is exactly the initial-moment
system. Positivity is needed only to ensure that there is a last coordinate. -/
theorem krylovRows_mulVec_eq_target_iff (hr : 0 < r)
    (A : Matrix (Fin d) (Fin d) R) (x y : Fin d → R) :
    (krylovRows r A x).mulVec y = krylovTarget r ↔
      (∀ k : ℕ, k < r - 1 → krylovMoment A x y k = 0) ∧
        krylovMoment A x y (r - 1) = -1 := by
  constructor
  · intro h
    constructor
    · intro k hk
      have hkr : k < r := by omega
      have hkne : k ≠ r - 1 := by omega
      have heq := congrFun h (⟨k, hkr⟩ : Fin r)
      simpa only [krylovRows_mulVec_apply, krylovTarget, Fin.val_mk, if_neg hkne] using heq
    · have hrm : r - 1 < r := by omega
      have heq := congrFun h (⟨r - 1, hrm⟩ : Fin r)
      simpa only [krylovRows_mulVec_apply, krylovTarget, Fin.val_mk, if_pos rfl] using heq
  · rintro ⟨hzero, hlast⟩
    funext k
    rw [krylovRows_mulVec_apply]
    change krylovMoment A x y k.val = if k.val = r - 1 then -1 else 0
    by_cases hk : k.val = r - 1
    · simpa only [hk, if_pos rfl] using hlast
    · rw [if_neg hk]
      apply hzero
      have hkr := k.isLt
      omega

/-- Any solution of the special target equation gives the explicit matrix
right inverse. -/
theorem krylov_mul_rightInverse_of_target (hr : 0 < r)
    (A : Matrix (Fin d) (Fin d) R) (x y : Fin d → R)
    (hy : (krylovRows r A x).mulVec y = krylovTarget r) :
    krylovRows r A x * krylovRightInverse r A x y = 1 := by
  rcases (krylovRows_mulVec_eq_target_iff hr A x y).mp hy with ⟨hzero, hlast⟩
  exact krylov_mul_rightInverse A x y hzero hlast

/-- Solvability of the single special Krylov target is equivalent to
surjectivity on ALL target vectors over any commutative ring. The backward
implication simply evaluates surjectivity at `krylovTarget r`. -/
theorem krylov_target_solvable_iff_surjective (hr : 0 < r)
    (A : Matrix (Fin d) (Fin d) R) (x : Fin d → R) :
    (∃ y : Fin d → R, (krylovRows r A x).mulVec y = krylovTarget r) ↔
      Function.Surjective (krylovRows r A x).mulVec := by
  constructor
  · rintro ⟨y, hy⟩
    exact mulVec_surjective_of_mul_eq_one _ _
      (krylov_mul_rightInverse_of_target hr A x y hy)
  · intro h
    exact h (krylovTarget r)

/-- The equivalent formulation directly in terms of moments. -/
theorem krylov_moments_solvable_iff_surjective (hr : 0 < r)
    (A : Matrix (Fin d) (Fin d) R) (x : Fin d → R) :
    (∃ y : Fin d → R,
      (∀ k : ℕ, k < r - 1 → krylovMoment A x y k = 0) ∧
        krylovMoment A x y (r - 1) = -1) ↔
      Function.Surjective (krylovRows r A x).mulVec := by
  rw [← krylov_target_solvable_iff_surjective hr A x]
  exact exists_congr fun y ↦ (krylovRows_mulVec_eq_target_iff hr A x y).symm

/-- Section 4's complete algebraic certificate in the dimensions of the
application: `d ≥ 2`, `r = d - 1`, and last moment `d - 2`.
The determinant, right inverse, and surjectivity are conclusions. -/
theorem krylov_certificate (hd : 2 ≤ d)
    (A : Matrix (Fin d) (Fin d) R) (x y : Fin d → R)
    (hzero : ∀ k : ℕ, k < d - 2 → krylovMoment A x y k = 0)
    (hlast : krylovMoment A x y (d - 2) = -1) :
    (krylovRows (d - 1) A x * krylovColumns (d - 1) A y).det =
        (-1 : R) ^ ((d - 1) * d / 2) ∧
      krylovRows (d - 1) A x * krylovRightInverse (d - 1) A x y = 1 ∧
      Function.Surjective (krylovRows (d - 1) A x).mulVec := by
  have hpred : d - 1 - 1 = d - 2 := by omega
  have hsucc : d - 1 + 1 = d := by omega
  have hz : ∀ k : ℕ, k < (d - 1) - 1 → krylovMoment A x y k = 0 := by
    simpa only [hpred] using hzero
  have hl : krylovMoment A x y ((d - 1) - 1) = -1 := by
    simpa only [hpred] using hlast
  refine ⟨?_, krylov_mul_rightInverse A x y hz hl,
    krylov_surjective_of_moments A x y hz hl⟩
  simpa only [hsucc] using krylov_product_det A x y hz hl

/-- In particular, the literal integral map `ℤ^d → ℤ^(d-1)` is surjective
if and only if ANY integral vector solves the single special target. -/
theorem integer_krylov_target_solvable_iff_surjective (hd : 2 ≤ d)
    (A : Matrix (Fin d) (Fin d) ℤ) (x : Fin d → ℤ) :
    (∃ y : Fin d → ℤ,
      (krylovRows (d - 1) A x).mulVec y = krylovTarget (d - 1)) ↔
      Function.Surjective (krylovRows (d - 1) A x).mulVec :=
  krylov_target_solvable_iff_surjective (by omega) A x

/-- The same integral equivalence written using the original moments. -/
theorem integer_krylov_moments_solvable_iff_surjective (hd : 2 ≤ d)
    (A : Matrix (Fin d) (Fin d) ℤ) (x : Fin d → ℤ) :
    (∃ y : Fin d → ℤ,
      (∀ k : ℕ, k < d - 2 → krylovMoment A x y k = 0) ∧
        krylovMoment A x y (d - 2) = -1) ↔
      Function.Surjective (krylovRows (d - 1) A x).mulVec := by
  have hpred : d - 1 - 1 = d - 2 := by omega
  simpa only [hpred] using
    krylov_moments_solvable_iff_surjective (r := d - 1) (by omega) A x

end Erdos975Support
