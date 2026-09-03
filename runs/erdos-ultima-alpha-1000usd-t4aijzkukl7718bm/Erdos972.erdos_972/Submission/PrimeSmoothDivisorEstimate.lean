import Submission.PrimeLeastFactorScales
import Submission.MixedSmoothMean

/-! A finite prime-input / smooth-output estimate. The long-divisor error
is explicit and is not assumed small at a prime-detecting parameter. -/
namespace Erdos972PrimeSmoothDivisorEstimate

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972PrimeLeastFactorScales Erdos972PrimeRoughOutputs
open Erdos972PrimePowerError Erdos972SmoothMangoldt Erdos972SmoothMangoldtPositive
open Erdos972SmoothDivisorTail Erdos972SmoothCorrelationApprox
open Erdos972DivisorCovariance Erdos972FixedDampedCorrelation
open Erdos972SelbergLowerTest Erdos972ExponentialSum

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable def primeExpSum (t α : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, primeWeight n*expDivisorSum t (floorMul α n)

noncomputable def primeTruncatedExpSum (t α : ℝ) (D N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, primeWeight n*truncatedExpSum t D (floorMul α n)

lemma primeExpSum_eq {α t : ℝ} (hα : 1 ≤ α) (ht : 0 < t) (N : ℕ) :
    primeExpSum t α N = t*mixedPrimeSmooth t α N := by
  unfold primeExpSum mixedPrimeSmooth
  rw [mul_sum]
  apply sum_congr rfl
  intro n hn
  by_cases hp : n.Prime
  · have hg1 : floorMul α n ≠ 1 := by
      have hh := self_le_floorMul hα n
      have hn2 := hp.two_le
      omega
    rw [smoothMangoldt, expDivisorSum_at_zero, one_apply, if_neg hg1, sub_zero]
    field_simp
  · simp [primeWeight, hp]

lemma primeTruncatedExpSum_eq {α : ℝ} (hα : 1 ≤ α) (t : ℝ) (D N : ℕ) :
    primeTruncatedExpSum t α D N =
      ∑ d ∈ Ioc 0 D, dampedCoefficient t d*row (Ioc 0 N) primeWeight (floorMul α) d := by
  classical
  unfold primeTruncatedExpSum
  have he (n : ℕ) (hn : n ∈ Ioc 0 N) :
      truncatedExpSum t D (floorMul α n) = divisorPolynomial D (dampedCoefficient t) (floorMul α n) :=
    truncatedExpSum_eq_polynomial t D (floorMul_pos hα (mem_Ioc.mp hn).1).ne'
  rw [sum_congr rfl (fun n hn => congrArg (fun x => primeWeight n*x) (he n hn))]
  simp only [divisorPolynomial, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro d hd
  unfold row
  rw [mul_sum]
  apply sum_congr rfl
  intro n hn
  by_cases hdn : d ∣ floorMul α n <;> simp [hdn, mul_comm]

lemma prime_truncated_discrepancy {α t E : ℝ} (hα : 1 ≤ α) (ht : 0 ≤ t) (hE : 0 ≤ E)
    (D N : ℕ)
    (hrows : ∀ d : ℕ, 0 < d → d ≤ D →
      |row (Ioc 0 N) primeWeight (floorMul α) d-Chebyshev.psi N/(d:ℝ)| ≤ E) :
    |primeTruncatedExpSum t α D N-Chebyshev.psi N*divisorMean D (dampedCoefficient t)| ≤ E*D := by
  rw [primeTruncatedExpSum_eq hα, divisorMean, mul_sum, ← sum_sub_distrib]
  have hterm (d : ℕ) : dampedCoefficient t d*row (Ioc 0 N) primeWeight (floorMul α) d-
      Chebyshev.psi N*(dampedCoefficient t d/d) =
      dampedCoefficient t d*(row (Ioc 0 N) primeWeight (floorMul α) d-Chebyshev.psi N/d) := by ring
  simp_rw [hterm]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ d ∈ Ioc 0 D, E := by
      apply sum_le_sum
      intro d hd
      rw [abs_mul]
      exact (mul_le_mul (abs_dampedCoefficient_le_one ht d)
        (hrows d (mem_Ioc.mp hd).1 (mem_Ioc.mp hd).2) (abs_nonneg _) zero_le_one).trans_eq (one_mul E)
    _ = _ := by simp only [sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]; ring

lemma primeWeight_le_prefix_log {N n : ℕ} (hn : n ∈ Ioc 0 N) :
    primeWeight n ≤ Real.log N := by
  unfold primeWeight
  split_ifs
  · exact monotone_log_natCast (mem_Ioc.mp hn).2
  · exact Real.log_natCast_nonneg N

/-- A finite long-divisor bound on genuine prime inputs. The logarithmic
factor is retained, as is the damping at the chosen divisor cutoff. -/
theorem prime_exp_tail_bound {α t : ℝ} (hα : 1 ≤ α) (ht : 0 ≤ t) (D N : ℕ) :
    |primeExpSum t α N-primeTruncatedExpSum t α D N| ≤
      Real.log N*damping t D*(floorMul α N:ℝ)*(1+Real.log (floorMul α N)) := by
  have he : primeExpSum t α N-primeTruncatedExpSum t α D N =
      ∑ n ∈ Ioc 0 N, primeWeight n*expTail t D (floorMul α n) := by
    simp only [primeExpSum, primeTruncatedExpSum, expTail, mul_sub, sum_sub_distrib]
  rw [he]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ n ∈ Ioc 0 N,
        (Real.log N*damping t D)*((floorMul α n).divisors.card:ℝ) := by
      apply sum_le_sum
      intro n hn
      rw [abs_mul, abs_of_nonneg (primeWeight_nonneg n)]
      have hh := mul_le_mul (primeWeight_le_prefix_log hn)
        (abs_expTail_le ht D (floorMul α n)) (abs_nonneg _) (Real.log_natCast_nonneg N)
      exact hh.trans_eq (by ring)
    _ = (Real.log N*damping t D)*(∑ n ∈ Ioc 0 N, ((floorMul α n).divisors.card:ℝ)) := (mul_sum ..).symm
    _ ≤ (Real.log N*damping t D)*((floorMul α N:ℝ)*(1+Real.log (floorMul α N))) :=
      mul_le_mul_of_nonneg_left (sum_output_divisors_le hα N)
        (mul_nonneg (Real.log_natCast_nonneg N) (damping_pos t D).le)
    _ = _ := by ring

/-- An actual two-sided mixed estimate, with its entire tail budget exposed.
It is not a uniform small-error theorem in the smoothing parameter. -/
theorem prime_smooth_finite_estimate {α t E : ℝ} (hα : 1 ≤ α) (ht : 0 < t) (hE : 0 ≤ E)
    (D N : ℕ)
    (hrows : ∀ d : ℕ, 0 < d → d ≤ D →
      |row (Ioc 0 N) primeWeight (floorMul α) d-Chebyshev.psi N/(d:ℝ)| ≤ E) :
    |t*mixedPrimeSmooth t α N-Chebyshev.psi N*divisorMean D (dampedCoefficient t)| ≤
      E*D+Real.log N*damping t D*(floorMul α N:ℝ)*(1+Real.log (floorMul α N)) := by
  have h₁ := prime_exp_tail_bound hα ht.le D N
  rw [primeExpSum_eq hα ht] at h₁
  have h₂ := prime_truncated_discrepancy hα ht.le hE D N hrows
  have hh := abs_sub_le (t*mixedPrimeSmooth t α N) (primeTruncatedExpSum t α D N)
    (Chebyshev.psi N*divisorMean D (dampedCoefficient t))
  linarith only [h₁, h₂, hh]

#print axioms prime_exp_tail_bound
#print axioms prime_smooth_finite_estimate

end Erdos972PrimeSmoothDivisorEstimate
