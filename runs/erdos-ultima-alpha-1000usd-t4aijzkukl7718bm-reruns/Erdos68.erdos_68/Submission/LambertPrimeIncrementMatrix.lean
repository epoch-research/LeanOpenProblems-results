import Submission.LambertPrimeBand
import Submission.PrimeLeadingForms

/-!
Simultaneous residue control for finite blocks of actual Lambert increments.
This is auxiliary arithmetic, not a proof or disproof of the conjecture.
The modulus is one prime; no simultaneous factorial clearing bound is asserted.
-/

namespace LambertPrimeIncrementMatrix

open Finset Erdos68Development PrimeLeadingForms

/-- A column-factorial-normalized increment matrix. -/
def binomialMatrix (p m : ℕ) : Matrix (Fin m) (Fin m) ℤ := fun i j =>
  (lambertCoeff (p+i.val-j.val)*(p+i.val).choose j.val : ℕ)

/-- The matrix obtained by scaling row i of the increment matrix by (p+i)!. -/
def rawMatrix (p m : ℕ) : Matrix (Fin m) (Fin m) ℤ := fun i j =>
  (lambertCoeff (p+i.val-j.val)*(p+i.val).descFactorial j.val : ℕ)

lemma choose_prime_translate {p i j : ℕ} (hp : p.Prime) (hi : i < p) (hj : j < p) :
    ((p+i).choose j : ZMod p) = (i.choose j : ZMod p) := by
  letI : Fact p.Prime := ⟨hp⟩
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := p+i) (k := j)
  have hmod : (p+i)%p=i := by simp [Nat.mod_eq_of_lt hi]
  have hdiv : (p+i)/p=1 := by
    rw [Nat.add_div_left _ hp.pos, Nat.div_eq_of_lt hi]
  simp only [hmod, hdiv, Nat.mod_eq_of_lt hj, Nat.div_eq_of_lt hj,
    Nat.choose_zero_right, mul_one] at h
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr h

/-- In a prime-sized band the normalized matrix is exactly Pascal's matrix modulo p. -/
theorem binomialMatrix_mod (p m : ℕ) (hp : p.Prime) (hm : m ≤ p) (i j : Fin m) :
    (binomialMatrix p m i j : ZMod p) = (i.val.choose j.val : ZMod p) := by
  have hi : i.val < p := i.isLt.trans_le hm
  have hj : j.val < p := j.isLt.trans_le hm
  simp only [binomialMatrix, Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
  rw [choose_prime_translate hp hi hj]
  by_cases hji : j.val ≤ i.val
  · have hn : p ≤ p+i.val-j.val := by omega
    have hn' : p+i.val-j.val < 2*p := by omega
    have ha := lambertCoeff_modEq_prime_band hp hn hn'
    have hc : (lambertCoeff (p+i.val-j.val) : ZMod p) = 1 := by
      simpa only [Nat.cast_one] using (ZMod.natCast_eq_natCast_iff _ 1 _).mpr ha
    rw [hc, one_mul]
  · rw [Nat.choose_eq_zero_of_lt (by omega : i.val < j.val)]
    simp

lemma rawMatrix_factor (p m : ℕ) (i j : Fin m) :
    rawMatrix p m i j = (j.val.factorial : ℤ)*binomialMatrix p m i j := by
  simp only [rawMatrix, binomialMatrix, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.cast_mul]
  ring

lemma rawMatrix_mod (p m : ℕ) (hp : p.Prime) (hm : m ≤ p) (i j : Fin m) :
    (rawMatrix p m i j : ZMod p) = (i.val.descFactorial j.val : ZMod p) := by
  rw [rawMatrix_factor, Int.cast_mul, Int.cast_natCast, binomialMatrix_mod p m hp hm]
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]

/-- No nonvanishing assumption about the original real sum enters this determinant. -/
theorem binomial_det_mod (p m : ℕ) (hp : p.Prime) (hm : m ≤ p) :
    (Matrix.det (fun i j : Fin m => (binomialMatrix p m i j : ZMod p))) = 1 := by
  let M : Matrix (Fin m) (Fin m) (ZMod p) := fun i j => (binomialMatrix p m i j : ZMod p)
  have htri : M.BlockTriangular OrderDual.toDual := by
    intro i j hij
    change i < j at hij
    rw [show M i j = (i.val.choose j.val : ZMod p) from binomialMatrix_mod p m hp hm i j]
    rw [Nat.choose_eq_zero_of_lt hij]
    simp only [Nat.cast_zero]
  change M.det = 1
  rw [Matrix.det_of_lowerTriangular M htri]
  simp only [M, binomialMatrix_mod p m hp hm, Nat.choose_self, Nat.cast_one, prod_const_one]

theorem raw_det_mod (p m : ℕ) (hp : p.Prime) (hm : m ≤ p) :
    (Matrix.det (fun i j : Fin m => (rawMatrix p m i j : ZMod p))) =
      ∏ i : Fin m, (i.val.factorial : ZMod p) := by
  let M : Matrix (Fin m) (Fin m) (ZMod p) := fun i j => (rawMatrix p m i j : ZMod p)
  have htri : M.BlockTriangular OrderDual.toDual := by
    intro i j hij
    change i < j at hij
    rw [show M i j = (i.val.descFactorial j.val : ZMod p) from rawMatrix_mod p m hp hm i j]
    rw [Nat.descFactorial_of_lt hij]
    simp only [Nat.cast_zero]
  change M.det = _
  rw [Matrix.det_of_lowerTriangular M htri]
  simp only [M, rawMatrix_mod p m hp hm, Nat.descFactorial_self]

lemma raw_det_mod_ne_zero (p m : ℕ) (hp : p.Prime) (hm : m ≤ p) :
    (Matrix.det (fun i j : Fin m => (rawMatrix p m i j : ZMod p))) ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [raw_det_mod p m hp hm]
  apply prod_ne_zero_iff.mpr
  intro i _ hi
  have hdiv : p ∣ i.val.factorial := (ZMod.natCast_eq_zero_iff _ _).mp hi
  have hc := hp.coprime_factorial_of_lt (i.isLt.trans_le hm)
  have hone := hc.eq_one_of_dvd hdiv
  exact hp.ne_one hone

/-- All m residues can be prescribed at once, with representatives less than p.
This only solves the displayed scaled system modulo p. -/
theorem simultaneous_residue_lift (p m : ℕ) (hp : p.Prime) (hm : m ≤ p)
    (v : Fin m → ZMod p) :
    ∃ w : Fin m → ℕ, (∀ j, w j < p) ∧
      ∀ i, ∑ j : Fin m, (rawMatrix p m i j : ZMod p)*(w j : ZMod p) = v i := by
  letI : Fact p.Prime := ⟨hp⟩
  let M : Matrix (Fin m) (Fin m) (ZMod p) := fun i j => (rawMatrix p m i j : ZMod p)
  have hdet : IsUnit M.det := isUnit_iff_ne_zero.mpr (raw_det_mod_ne_zero p m hp hm)
  have hs : Function.Surjective M.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det M).mpr hdet)
  obtain ⟨u, hu⟩ := hs v
  refine ⟨fun j => (u j).val, fun j => ZMod.val_lt _, ?_⟩
  intro i
  simp only [ZMod.natCast_zmod_val]
  exact congrFun hu i

/-- The integer entries are exactly scaled increments of the original Lambert prefix. -/
theorem rawMatrix_prefix_identity (p m : ℕ) (hm : m ≤ p)
    (i j : Fin m) :
    (rawMatrix p m i j : ℚ) = ((p+i.val).factorial : ℚ)*
      (partialSum (fun n => (lambertCoeff n : ℤ)) (p+i.val-j.val) -
        partialSum (fun n => (lambertCoeff n : ℤ)) (p+i.val-j.val-1)) := by
  have hj : j.val ≤ p+i.val := by have := j.isLt; omega
  have hn : 0 < p+i.val-j.val := by have := j.isLt; omega
  rw [partialSum_step _ _ hn]
  simp only [add_sub_cancel_left, Int.cast_natCast]
  simp only [rawMatrix, Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
  rw [Nat.descFactorial_eq_div hj]
  rw [Nat.cast_div (Nat.factorial_dvd_factorial (Nat.sub_le _ _)) (by positivity)]
  ring

end LambertPrimeIncrementMatrix

#print axioms LambertPrimeIncrementMatrix.binomial_det_mod
#print axioms LambertPrimeIncrementMatrix.raw_det_mod_ne_zero
#print axioms LambertPrimeIncrementMatrix.simultaneous_residue_lift
#print axioms LambertPrimeIncrementMatrix.rawMatrix_prefix_identity
