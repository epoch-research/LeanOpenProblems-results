import Submission.CorrelationVaughan

/-! Exact divisor renewal and Möbius inversion across integer dilates of a
slope. These identities do not assert a prime-pair lower bound. -/
namespace Erdos972PrimeCorrelationRenewal

open Finset ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.Moebius
open Erdos972PrimePowerError Erdos972CorrelationVaughan

noncomputable def logarithmicOutputMass (α : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, Real.log n * Λ (floorMul α n)

lemma floorMul_mul (α : ℝ) (m n : ℕ) :
    floorMul α (m * n) = floorMul (α * m) n := by
  simp only [floorMul, Nat.cast_mul, mul_assoc]

/-- The first cofactor, `m = 1`, is exactly the original two-Mangoldt
correlation. All other terms are nonnegative correlations at dilated slopes. -/
theorem logarithmicOutputMass_renewal (α : ℝ) (N : ℕ) :
    logarithmicOutputMass α N =
      ∑ m ∈ Ioc 0 N, mangoldtCorrelation (α * m) (N / m) := by
  have h := weightedSum_convolution (ζ : ArithmeticFunction ℝ) Λ
    (fun n => Λ (floorMul α n)) N
  rw [zeta_mul_vonMangoldt] at h
  change logarithmicOutputMass α N = _ at h
  rw [h]
  apply sum_congr rfl
  intro m hm
  rw [natCoe_apply, zeta_apply_ne (Nat.ne_of_gt (mem_Ioc.mp hm).1)]
  simp only [Nat.cast_one, one_mul, floorMul_mul, mangoldtCorrelation]

/-- Inverting the positive renewal sum restores signed Möbius coefficients;
positivity of the logarithmic output mass does not remove these signs. -/
theorem mangoldtCorrelation_inversion (α : ℝ) (N : ℕ) :
    mangoldtCorrelation α N =
      ∑ m ∈ Ioc 0 N, (μ m : ℝ) * logarithmicOutputMass (α * m) (N / m) := by
  have h := weightedSum_convolution (μ : ArithmeticFunction ℝ) ArithmeticFunction.log
    (fun n => Λ (floorMul α n)) N
  rw [moebius_mul_log_eq_vonMangoldt] at h
  change mangoldtCorrelation α N = _ at h
  simpa only [intCoe_apply, ArithmeticFunction.log_apply,
    floorMul_mul, logarithmicOutputMass] using h

lemma mangoldtCorrelation_nonneg (α : ℝ) (N : ℕ) :
    0 ≤ mangoldtCorrelation α N := by
  exact sum_nonneg fun _ _ => mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg

/-- Isolate the original slope while retaining every other cofactor. -/
theorem logarithmicOutputMass_sub_dilates (α : ℝ) {N : ℕ} (hN : 0 < N) :
    logarithmicOutputMass α N -
      ∑ m ∈ Ioc 1 N, mangoldtCorrelation (α * m) (N / m) =
        mangoldtCorrelation α N := by
  rw [logarithmicOutputMass_renewal]
  have hsum := sum_Ioc_consecutive (fun m : ℕ =>
    mangoldtCorrelation (α * m) (N / m)) (show 0 ≤ 1 by omega) hN
  simp only [Nat.Ioc_succ_singleton, sum_singleton, Nat.zero_add, Nat.cast_one, mul_one, Nat.div_one] at hsum
  linarith

#print axioms logarithmicOutputMass_renewal
#print axioms mangoldtCorrelation_inversion
#print axioms logarithmicOutputMass_sub_dilates
end Erdos972PrimeCorrelationRenewal
