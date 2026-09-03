import Submission.SelbergSignedOptimum

/-! A kernel-checked global signed optimum in the six-prime example.
The improvement here is finite and less than one part per million. -/
namespace Erdos970.SelbergSignedExample
open Finset

def optimumCutoff : ℚ := 84045836 / 3477
def optimumNormalizer : ℚ := 524479326553 / 4172400

def optimum (Q : Pattern) : ℚ :=
  (if Q = univ then -(optimumCutoff - 19740) / 14400
   else if Q = univ.erase 0 ∨ Q = univ.erase 1 then (optimumCutoff - 19740) / 14400
   else (optimumCutoff - height Q) / variance Q) / optimumNormalizer

def optimumDual (T : Pattern) : ℚ :=
  if T = univ then -1
  else if T = univ.erase 1 then -11304661 / 12430275
  else if T = univ.erase 0 then -4270223 / 12430275
  else (-1) ^ T.card

def transformMatrix (T Q : Pattern) : ℚ :=
  if T ⊆ Q then (-1) ^ T.card * primeProduct T else 0

def optimumAdjoint (Q : Pattern) : ℚ :=
  ∑ T : Pattern, optimumDual T * transformMatrix T Q

def optimumValue : ℚ := 94136607674833920 / 74925618079

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- A rational primal-dual certificate, checked by the kernel. -/
theorem optimum_certificate :
    (∑ Q : Pattern, optimum Q) = 1 ∧
    (∀ T : Pattern, |optimumDual T| ≤ 1) ∧
    (∀ T : Pattern, optimumDual T * ordinary optimum T = |ordinary optimum T|) ∧
    (∀ Q : Pattern, (32668496 / 5) * variance Q * optimum Q +
      cost optimum * optimumAdjoint Q = optimumValue) ∧
    objective optimum = optimumValue ∧
    objective base / (∑ Q : Pattern, base Q) ^ 2 =
      (4045983376266 / 4045981553225) * optimumValue := by
  decide +kernel

lemma matrix_image (c : Pattern → ℝ) (T : Pattern) :
    SelbergSignedOptimum.image (fun T Q => (transformMatrix T Q : ℝ)) c T =
      FiniteSelberg.ordinaryCoefficient marginal c T := by
  simp only [SelbergSignedOptimum.image, transformMatrix,
    apply_ite (fun x : ℚ => (x : ℝ)), Rat.cast_mul, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_one, Rat.cast_zero, primeProduct, Rat.cast_prod,
    Rat.cast_natCast, FiniteSelberg.ordinaryCoefficient, marginal,
    div_eq_mul_inv, one_mul, prod_inv_distrib, inv_inv, mul_sum]
  apply sum_congr rfl
  intro Q hQ
  split_ifs <;> ring

lemma matrix_cost (c : Pattern → ℝ) :
    SelbergSignedOptimum.cost (fun T Q => (transformMatrix T Q : ℝ)) c =
      FiniteSelberg.kernelCost marginal c := by
  simp only [SelbergSignedOptimum.cost, FiniteSelberg.kernelCost, matrix_image]

lemma matrix_adjoint (Q : Pattern) :
    SelbergSignedOptimum.adjoint (fun T Q => (transformMatrix T Q : ℝ))
      (fun T => (optimumDual T : ℝ)) Q = (optimumAdjoint Q : ℝ) := by
  simp only [SelbergSignedOptimum.adjoint, optimumAdjoint, Rat.cast_sum, Rat.cast_mul]

lemma matrix_objective (c : Pattern → ℝ) :
    SelbergSignedOptimum.objective (fun Q => (variance Q : ℝ))
      (fun T Q => (transformMatrix T Q : ℝ)) (32668496 / 5) c = sieveObjective c := by
  have havg : FiniteSelberg.average marginal (fun ω =>
      FiniteSelberg.linearKernel marginal c ω ^ 2) = ∑ Q : Pattern, (variance Q : ℝ) * c Q ^ 2 := by
    rw [show (fun ω => FiniteSelberg.linearKernel marginal c ω ^ 2) =
      (fun ω => (∑ Q : Pattern, c Q * FiniteSelberg.basis marginal Q ω) ^ 2) by rfl,
      FiniteSelberg.average_square_sum marginal (fun i => (marginal_bounds i).1.ne')]
    simp only [real_variance, mul_comm]
  simp only [SelbergSignedOptimum.objective, sieveObjective, matrix_cost, havg]

/-- This is a global optimum over all real signed orthogonal coefficients
normalized to take value one at the empty hit pattern. -/
theorem optimum_minimizes_all (c : Pattern → ℝ) (hsum : (∑ Q : Pattern, c Q) = 1) :
    sieveObjective (fun Q => (optimum Q : ℝ)) ≤ sieveObjective c := by
  rw [← matrix_objective, ← matrix_objective]
  apply SelbergSignedOptimum.minimizes_all
    (fun Q => (variance Q : ℝ)) (fun T Q => (transformMatrix T Q : ℝ)) (32668496 / 5)
    (fun Q => le_of_lt (Rat.cast_pos.mpr (positive_certificate.1 Q))) (by positivity)
    (fun Q => (optimum Q : ℝ)) (fun T => (optimumDual T : ℝ)) (optimumValue : ℝ)
  · intro T
    have h := (Rat.cast_le (K := ℝ)).mpr (optimum_certificate.2.1 T)
    simpa only [Rat.cast_abs, Rat.cast_one] using h
  · intro T
    rw [matrix_image, real_ordinary]
    have h := congrArg (fun x : ℚ => (x : ℝ)) (optimum_certificate.2.2.1 T)
    simpa only [Rat.cast_mul, Rat.cast_abs] using h
  · intro Q
    rw [matrix_cost, real_cost, matrix_adjoint]
    have h := congrArg (fun x : ℚ => (x : ℝ)) (optimum_certificate.2.2.2.1 Q)
    simpa only [Rat.cast_mul, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat] using h
  · rw [hsum]
    exact_mod_cast optimum_certificate.1.symm

lemma sieveObjective_rational (c : Pattern → ℚ) :
    sieveObjective (fun Q => (c Q : ℝ)) = (objective c : ℝ) := by
  simp only [sieveObjective, real_meanSquare, real_cost, objective,
    Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow]

/-- The numerical value of the global signed optimum is exact. -/
theorem optimum_value : sieveObjective (fun Q => (optimum Q : ℝ)) = (optimumValue : ℝ) := by
  rw [sieveObjective_rational, optimum_certificate.2.2.2.2.1]

/-- At this parameter, even unrestricted signed kernels improve on the best
nonnegative profile by less than one part per million. No asymptotic conclusion
is drawn from this finite example. -/
theorem optimum_gain :
    sieveObjective (fun Q => (optimum Q : ℝ)) <
      sieveObjective (fun Q => (base Q : ℝ)) / (∑ Q : Pattern, (base Q : ℝ)) ^ 2 ∧
    sieveObjective (fun Q => (base Q : ℝ)) / (∑ Q : Pattern, (base Q : ℝ)) ^ 2 <
      (1 + 1 / 1000000) * sieveObjective (fun Q => (optimum Q : ℝ)) := by
  simp only [sieveObjective_rational, optimum_certificate.2.2.2.2.1]
  have heq : (objective base : ℝ) / (∑ Q : Pattern, (base Q : ℝ)) ^ 2 =
      (4045983376266 / 4045981553225) * (optimumValue : ℝ) := by
    have h := congrArg (fun x : ℚ => (x : ℝ)) (optimum_certificate.2.2.2.2.2)
    simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_sum, Rat.cast_mul, Rat.cast_ofNat] using h
  rw [heq]
  norm_num [optimumValue]

#print axioms optimum_certificate
#print axioms optimum_minimizes_all
#print axioms optimum_gain
end Erdos970.SelbergSignedExample
