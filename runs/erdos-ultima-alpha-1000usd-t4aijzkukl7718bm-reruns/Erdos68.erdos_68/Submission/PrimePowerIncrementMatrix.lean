import Submission.LambertPrimeIncrementMatrix
import Submission.FilteredPeriodicUnits

/-!
Prime-power local control for column-factorial-normalized increment matrices.
These are auxiliary local statements, not a settlement of Erdos 68.
The normalization and the remaining global denominator costs are explicit.
-/

namespace PrimePowerIncrementMatrix

open Finset Erdos68Development PrimeLeadingForms

/-- Lucas reduction below a whole prime-power block. -/
lemma choose_translate (p r t i j : ℕ) (hp : p.Prime)
    (hi : i < p^r) (hj : j < p^r) :
    Nat.ModEq p ((p^r*t+i).choose j) (i.choose j) := by
  letI : Fact p.Prime := ⟨hp⟩
  induction r generalizing i j with
  | zero =>
    have hi0 : i=0 := by simpa using hi
    have hj0 : j=0 := by simpa using hj
    subst i; subst j
    simp only [Nat.choose_zero_right]
    rfl
  | succ r ih =>
    have hid : i/p < p^r := by
      apply (Nat.div_lt_iff_lt_mul hp.pos).mpr
      simpa only [pow_succ] using hi
    have hjd : j/p < p^r := by
      apply (Nat.div_lt_iff_lt_mul hp.pos).mpr
      simpa only [pow_succ] using hj
    have ht : p^(r+1)*t+i = p*(p^r*t)+i := by rw [pow_succ']; ring
    rw [ht]
    have h₁ := Choose.choose_modEq_choose_mod_mul_choose_div_nat
      (p := p) (n := p*(p^r*t)+i) (k := j)
    have h₂ := Choose.choose_modEq_choose_mod_mul_choose_div_nat
      (p := p) (n := i) (k := j)
    have hh := (Nat.ModEq.refl ((i%p).choose (j%p))).mul (ih (i/p) (j/p) hid hjd)
    simp only [Nat.mul_add_mod, Nat.mul_add_div hp.pos] at h₁
    exact h₁.trans (hh.trans h₂.symm)

/-- These are integer entries, but their input normalization is 1/j!. -/
def normalized (c : ℕ → ℤ) (N m : ℕ) : Matrix (Fin m) (Fin m) ℤ := fun i j =>
  ((N+i.val).choose j.val : ℤ)*c (N+i.val-j.val)

/-- Only the central coefficient needs to be a unit congruent to one.
No congruence for the coefficients below the diagonal is assumed. -/
theorem determinant_one_mod (c : ℕ → ℤ) (p r t m : ℕ) (hp : p.Prime)
    (hm : m ≤ p^r) (hc : (c (p^r*t) : ZMod p)=1) :
    (Matrix.det (fun i j : Fin m => (normalized c (p^r*t) m i j : ZMod p))) = 1 := by
  let M : Matrix (Fin m) (Fin m) (ZMod p) :=
    fun i j => (normalized c (p^r*t) m i j : ZMod p)
  have he (i j : Fin m) : M i j =
      (i.val.choose j.val : ZMod p)*(c (p^r*t+i.val-j.val) : ZMod p) := by
    simp only [M, normalized, Int.cast_mul, Int.cast_natCast]
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr
      (choose_translate p r t i.val j.val hp (i.isLt.trans_le hm) (j.isLt.trans_le hm))]
  have htri : M.BlockTriangular OrderDual.toDual := by
    intro i j hij
    change i < j at hij
    rw [he, Nat.choose_eq_zero_of_lt hij, Nat.cast_zero, zero_mul]
  change M.det=1
  rw [Matrix.det_of_lowerTriangular M htri]
  have hdiag (i : Fin m) : M i i=1 := by
    rw [he, Nat.choose_self, Nat.cast_one, Nat.add_sub_cancel, hc, one_mul]
  simp only [hdiag, prod_const_one]

/-- The same normalized matrix is invertible modulo every power of p.
Representatives solve all m congruences simultaneously and are less than p^e. -/
theorem prime_power_residue_lift (c : ℕ → ℤ) (p r t m e : ℕ) (hp : p.Prime)
    (hm : m ≤ p^r) (hc : (c (p^r*t) : ZMod p)=1)
    (v : Fin m → ZMod (p^e)) :
    ∃ w : Fin m → ℕ, (∀ j, w j < p^e) ∧
      ∀ i, ∑ j : Fin m, (normalized c (p^r*t) m i j : ZMod (p^e))*
        (w j : ZMod (p^e)) = v i := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero (p^e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let A := normalized c (p^r*t) m
  have he : (A.det : ZMod p)=1 := by
    change (Int.castRingHom (ZMod p)) A.det=1
    rw [RingHom.map_det]
    exact determinant_one_mod c p r t m hp hm hc
  have hu : IsUnit (A.det : ZMod p) := by rw [he]; exact isUnit_one
  have hcop : IsCoprime (p : ℤ) A.det :=
    (ZMod.coe_int_isUnit_iff_isCoprime A.det p).mp hu
  have hcop' : IsCoprime ((p^e : ℕ) : ℤ) A.det := by
    simpa only [Nat.cast_pow] using (hcop.pow_left (m := e))
  have hu' : IsUnit (A.det : ZMod (p^e)) :=
    (ZMod.coe_int_isUnit_iff_isCoprime A.det (p^e)).mpr hcop'
  let M := (Int.castRingHom (ZMod (p^e))).mapMatrix A
  have hdet : IsUnit M.det := by
    dsimp only [M]
    rw [← RingHom.map_det]
    exact hu'
  have hs : Function.Surjective M.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det M).mpr hdet)
  obtain ⟨u, hu⟩ := hs v
  refine ⟨fun j => (u j).val, fun j => ZMod.val_lt _, ?_⟩
  intro i
  simp only [ZMod.natCast_zmod_val]
  exact congrFun hu i

/-- Explicit connection with factorial-series prefix increments.
The input column factor 1/j! cannot be omitted when applying this identity. -/
theorem normalized_prefix_identity (c : ℕ → ℤ) (N m : ℕ) (hm : m ≤ N)
    (i j : Fin m) :
    (normalized c N m i j : ℚ) = ((N+i.val).factorial : ℚ)/j.val.factorial *
      (partialSum c (N+i.val-j.val)-partialSum c (N+i.val-j.val-1)) := by
  have hj : j.val ≤ N+i.val := by have := j.isLt; omega
  have hn : 0 < N+i.val-j.val := by have := j.isLt; omega
  rw [partialSum_step _ _ hn]
  simp only [add_sub_cancel_left, normalized, Int.cast_mul, Int.cast_natCast]
  rw [Nat.cast_choose ℚ hj]
  ring

/-- Restoring ordinary integral input weights restores the column factorials. -/
def unnormalized (c : ℕ → ℤ) (N m : ℕ) : Matrix (Fin m) (Fin m) ℤ :=
  fun i j => (j.val.factorial : ℤ)*normalized c N m i j

lemma unnormalized_prefix_identity (c : ℕ → ℤ) (N m : ℕ) (hm : m ≤ N)
    (i j : Fin m) :
    (unnormalized c N m i j : ℚ) = ((N+i.val).factorial : ℚ)*
      (partialSum c (N+i.val-j.val)-partialSum c (N+i.val-j.val-1)) := by
  simp only [unnormalized, Int.cast_mul, Int.cast_natCast]
  rw [normalized_prefix_identity c N m hm]
  have hfac : (j.val.factorial : ℚ) ≠ 0 := by positivity
  field_simp

/-- A small prime sees a zero column once the input normalization is removed. -/
theorem unnormalized_det_zero (c : ℕ → ℤ) (N m p : ℕ) (hp : p.Prime)
    (hpm : p < m) :
    (Matrix.det (fun i j : Fin m => (unnormalized c N m i j : ZMod p))) = 0 := by
  apply Matrix.det_eq_zero_of_column_eq_zero (⟨p, hpm⟩ : Fin m)
  intro i
  simp only [unnormalized, Int.cast_mul, Int.cast_natCast]
  have hf : (p.factorial : ZMod p)=0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.dvd_factorial hp.pos le_rfl)
  rw [hf, zero_mul]

/-- In particular the normalized local surjectivity cannot be transferred to
ordinary integral prefix-increment weights at all small primes. -/
theorem unnormalized_not_surjective (c : ℕ → ℤ) (N m p : ℕ) (hp : p.Prime)
    (hpm : p < m) :
    ¬ Function.Surjective
      (fun w : Fin m → ZMod p => fun i =>
        ∑ j : Fin m, (unnormalized c N m i j : ZMod p)*w j) := by
  letI : Fact p.Prime := ⟨hp⟩
  let M : Matrix (Fin m) (Fin m) (ZMod p) :=
    fun i j => (unnormalized c N m i j : ZMod p)
  intro hs
  have hsurj : Function.Surjective M.mulVec := hs
  have hunit : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp
    (Matrix.mulVec_surjective_iff_isUnit.mp hsurj)
  exact hunit.ne_zero (unnormalized_det_zero c N m p hp hpm)

/-- The original Lambert coefficients meet the central-unit condition on
an explicit progression of centers, not just at one initial prime. -/
theorem lambert_prime_power_lift (p r t m e : ℕ) (hp : p.Prime)
    (hm : m ≤ p^(r+1)) (v : Fin m → ZMod (p^e)) :
    ∃ w : Fin m → ℕ, (∀ j, w j < p^e) ∧
      ∀ i, ∑ j : Fin m,
        (normalized (fun n => (lambertCoeff n : ℤ)) (p^(r+1)*(p*t+1)) m i j :
          ZMod (p^e))*(w j : ZMod (p^e)) = v i := by
  apply prime_power_residue_lift _ p (r+1) (p*t+1) m e hp hm _ v
  have h := FilteredPeriodicUnits.lambertCoeff_periodic_unit p r t hp
  simpa only [Int.cast_natCast, Nat.cast_one] using
    (ZMod.natCast_eq_natCast_iff _ 1 p).mpr h

/-- Previously cancelled rows can be retained at the coefficient level:
the same result holds for the exact binomial-filtered Lambert coefficients. -/
theorem filtered_prime_power_lift (ks : List ℕ) (p r t m e : ℕ) (hp : p.Prime)
    (hm : m ≤ p^(r+1)) (hks : ∀ k ∈ ks, 0 < k ∧ k < p^(r+1))
    (v : Fin m → ZMod (p^e)) :
    ∃ w : Fin m → ℕ, (∀ j, w j < p^e) ∧
      ∀ i, ∑ j : Fin m,
        (normalized (BinomialFilteredLambert.filtered ks) (p^(r+1)*(p*t+1)) m i j :
          ZMod (p^e))*(w j : ZMod (p^e)) = v i := by
  apply prime_power_residue_lift _ p (r+1) (p*t+1) m e hp hm _ v
  have h := FilteredPeriodicUnits.filtered_periodic_unit ks p r t hp hks
  simpa only [Int.cast_one] using (ZMod.intCast_eq_intCast_iff _ 1 p).mpr h

end PrimePowerIncrementMatrix

#print axioms PrimePowerIncrementMatrix.determinant_one_mod
#print axioms PrimePowerIncrementMatrix.prime_power_residue_lift
#print axioms PrimePowerIncrementMatrix.normalized_prefix_identity
#print axioms PrimePowerIncrementMatrix.unnormalized_det_zero
#print axioms PrimePowerIncrementMatrix.unnormalized_not_surjective
#print axioms PrimePowerIncrementMatrix.lambert_prime_power_lift
#print axioms PrimePowerIncrementMatrix.filtered_prime_power_lift
