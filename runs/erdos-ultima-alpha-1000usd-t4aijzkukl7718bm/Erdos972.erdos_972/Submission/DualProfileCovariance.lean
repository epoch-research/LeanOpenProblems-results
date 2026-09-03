import Submission.DualPrimeRows
import Submission.ProfileLogShift

/-! Covariance of a prime input with a logarithmic divisor profile at the
output. Weighted and unweighted one-prime moments are kept separate. -/
namespace Erdos972DualProfileCovariance

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972DualPrimeRows Erdos972DivisorCovariance Erdos972LogarithmicCovariance
open Erdos972LogDivisorProfiles Erdos972PrimePowerError Erdos972TypeIPolynomial
open Erdos972SelfCenteredLog Erdos972CommonLogCenter Erdos972ChebyshevRowMean
open Erdos972ChebyshevPNT Erdos972DivisorPairCount

set_option maxHeartbeats 1000000

lemma prime_polynomial_expansion (α : ℝ) (N E : ℕ) (c : ℕ → ℝ) :
    total N (fun n => vonMangoldt n*divisorPolynomial E c (floorMul α n)) =
      ∑ e ∈ Ioc 0 E, c e*inputDivisorRow α e N := by
  simp only [total, divisorPolynomial, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro e he
  simp only [inputDivisorRow, sum_filter, mul_sum]
  apply sum_congr rfl
  intro n hn
  split_ifs <;> ring

lemma prime_polynomial_moment (α : ℝ) (N E : ℕ) (c : ℕ → ℝ) {B : ℝ}
    (hrows : ∀ e ∈ Ioc 0 E, |inputDivisorRow α e N-Chebyshev.psi N/e| ≤ B) :
    |total N (fun n => vonMangoldt n*divisorPolynomial E c (floorMul α n))-
      divisorMean E c*Chebyshev.psi N| ≤ B*coefficientMass E c := by
  have he : total N (fun n => vonMangoldt n*divisorPolynomial E c (floorMul α n))-
      divisorMean E c*Chebyshev.psi N =
        ∑ e ∈ Ioc 0 E, c e*(inputDivisorRow α e N-Chebyshev.psi N/e) := by
    rw [prime_polynomial_expansion]
    simp only [divisorMean, sum_mul, ← sum_sub_distrib]
    apply sum_congr rfl
    intro e he
    ring
  rw [he]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ e ∈ Ioc 0 E, B*|c e| := by
      apply sum_le_sum
      intro e he
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hrows e he) (abs_nonneg _)).trans_eq (by ring)
    _ = _ := by rw [coefficientMass, mul_sum]

lemma prime_log_polynomial_moment (α : ℝ) (N E : ℕ) (c : ℕ → ℝ) {B : ℝ}
    (hrows : ∀ j ≤ N, ∀ e ∈ Ioc 0 E, |inputDivisorRow α e j-Chebyshev.psi j/e| ≤ B) :
    |total N (fun n => Real.log n*(vonMangoldt n*divisorPolynomial E c (floorMul α n)))-
      divisorMean E c*logRow (fun n => vonMangoldt n) N| ≤ 2*Real.log N*(B*coefficientMass E c) := by
  have hh := logRow_prefix_approx (fun n => vonMangoldt n*divisorPolynomial E c (floorMul α n))
    (fun j => divisorMean E c*Chebyshev.psi j) (by simp [Chebyshev.psi]) N (B*coefficientMass E c)
    (fun j hj => prime_polynomial_moment α j E c (hrows j hj))
  have he : logIncrement (fun j => divisorMean E c*Chebyshev.psi j) N =
      divisorMean E c*logRow (fun n => vonMangoldt n) N := by
    rw [← logIncrement_psi]
    simp only [logIncrement, mul_sum]
    apply sum_congr rfl
    intro n hn
    ring
  rwa [he] at hh

lemma prime_aligned_moment (α : ℝ) (N E : ℕ) (c d : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hrows : ∀ j ≤ N, ∀ e ∈ Ioc 0 E, |inputDivisorRow α e j-Chebyshev.psi j/e| ≤ B) :
    |total N (fun n => vonMangoldt n*alignedOutput α E c d n)-
      total N (fun n => vonMangoldt n*model E c d n)| ≤ 2*(1+Real.log N)*B*profileMass E c d := by
  have hc := prime_log_polynomial_moment α N E c hrows
  have hd := prime_polynomial_moment α N E d (hrows N le_rfl)
  have he : total N (fun n => vonMangoldt n*alignedOutput α E c d n)-
      total N (fun n => vonMangoldt n*model E c d n) =
      (total N (fun n => Real.log n*(vonMangoldt n*divisorPolynomial E c (floorMul α n)))-
        divisorMean E c*logRow (fun n => vonMangoldt n) N)+
      (total N (fun n => vonMangoldt n*divisorPolynomial E d (floorMul α n))-
        divisorMean E d*Chebyshev.psi N) := by
    simp only [total, logRow, alignedOutput, model, Chebyshev.psi, Nat.floor_natCast,
      mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro n hn
    ring
  rw [he]
  apply (abs_add_le _ _).trans
  unfold profileMass
  nlinarith only [hc, hd, mul_nonneg hB (coefficientMass_nonneg E c),
    mul_nonneg hB (coefficientMass_nonneg E d),
    mul_nonneg (Real.log_natCast_nonneg N) (mul_nonneg hB (coefficientMass_nonneg E d))]

lemma total_mangoldt (N : ℕ) : total N (fun n => vonMangoldt n) = Chebyshev.psi N := by
  simp only [total, Chebyshev.psi, Nat.floor_natCast]

lemma mangoldt_covariance_perturb {N : ℕ} (hN : 0 < N) (g G : ℕ → ℝ) {E₁ E₂ : ℝ}
    (h₁ : |total N g-total N G| ≤ E₁)
    (h₂ : |total N (fun n => vonMangoldt n*g n)-total N (fun n => vonMangoldt n*G n)| ≤ E₂) :
    |covariance N (fun n => vonMangoldt n) g-covariance N (fun n => vonMangoldt n) G| ≤ E₂+7*E₁ := by
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have he : covariance N (fun n => vonMangoldt n) g-covariance N (fun n => vonMangoldt n) G =
      (total N (fun n => vonMangoldt n*g n)-total N (fun n => vonMangoldt n*G n))-
        (Chebyshev.psi N/N)*(total N g-total N G) := by
    unfold covariance
    rw [total_mangoldt]
    ring
  rw [he]
  apply (abs_sub _ _).trans
  rw [abs_mul, abs_of_nonneg (psi_ratio_bounds hNR).1]
  have hm := mul_le_mul (psi_ratio_bounds hNR).2 h₁ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 7)
  linarith only [h₂, hm]

lemma covariance_model_right {N : ℕ} (hN : 0 < N) (f : ℕ → ℝ) (E : ℕ) (c d : ℕ → ℝ) :
    covariance N f (model E c d) = divisorMean E c*covariance N f (fun n => Real.log n) := by
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  unfold covariance
  rw [total_model]
  have hp : total N (fun n => f n*model E c d n) =
      divisorMean E c*total N (fun n => f n*Real.log n)+divisorMean E d*total N f := by
    simp only [total, model, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro n hn
    ring
  rw [hp]
  unfold total
  field_simp
  ring

lemma mangoldt_log_covariance (N : ℕ) :
    covariance N (fun n => vonMangoldt n) (fun n => Real.log n) =
      selfCenteredLog (fun j : ℕ => Chebyshev.psi j) N := by
  have he : selfCenteredLog (fun j : ℕ => Chebyshev.psi j) N =
      logIncrement (fun j : ℕ => Chebyshev.psi j) N-(Chebyshev.psi N/N)*logMass N := by
    simp only [selfCenteredLog, logIncrement, logMass,
      Erdos972ExponentialSum.sum_Ioc_zero_eq_sum_range_succ, mul_sub, sum_sub_distrib, ← sum_mul]
    ring
  rw [he, logIncrement_psi, covariance, total_mangoldt]
  simp only [total, logRow, logMass]
  have hh : (∑ n ∈ Ioc 0 N, vonMangoldt n*Real.log n) = ∑ n ∈ Ioc 0 N, Real.log n*vonMangoldt n := by
    apply sum_congr rfl
    intro n hn
    ring
  rw [hh]
  ring

lemma mangoldt_log_covariance_tendsto :
    Tendsto (fun N : ℕ => covariance N (fun n => vonMangoldt n) (fun n => Real.log n)/N)
      atTop (𝓝 0) := by
  simp_rw [mangoldt_log_covariance]
  exact selfCenteredLog_div_tendsto _ (by simp [Chebyshev.psi])
    (psi_div_self_tendsto.comp tendsto_natCast_atTop_atTop)

/-- The only main covariance is a signed coefficient times the scalar
prime/log covariance, which is sublinear by qualitative PNT. -/
theorem prime_aligned_covariance (α : ℝ) {N D E : ℕ} (hN : 0 < N) (hD : 0 < D)
    (c d : ℕ → ℝ) {Bp Bd : ℝ} (hBp : 0 ≤ Bp) (hBd : 0 ≤ Bd)
    (hrows : ∀ j ≤ N, ∀ e ∈ Ioc 0 E, |inputDivisorRow α e j-Chebyshev.psi j/e| ≤ Bp)
    (hlocal : ∀ j ≤ N, ∀ a ∈ Ioc 0 D, ∀ b ∈ Ioc 0 E,
      |((divisorPairs α j a b).card : ℝ)-(j : ℝ)/(a*b)| ≤ Bd) :
    |covariance N (fun n => vonMangoldt n) (alignedOutput α E c d)| ≤
      |divisorMean E c| * |covariance N (fun n => vonMangoldt n) (fun n => Real.log n)|+
        2*(1+Real.log N)*(Bp+7*Bd)*profileMass E c d := by
  have hg := aligned_first_moment α hD c d hBd hlocal
  have hw := prime_aligned_moment α N E c d hBp hrows
  have hc := mangoldt_covariance_perturb hN (alignedOutput α E c d) (model E c d) hg hw
  have ht := abs_sub_le (covariance N (fun n => vonMangoldt n) (alignedOutput α E c d))
    (covariance N (fun n => vonMangoldt n) (model E c d)) 0
  simp only [sub_zero, covariance_model_right hN, abs_mul] at ht
  rw [covariance_model_right hN] at hc
  nlinarith only [hc, ht]

#print axioms prime_aligned_covariance
#print axioms mangoldt_log_covariance_tendsto

end Erdos972DualProfileCovariance
