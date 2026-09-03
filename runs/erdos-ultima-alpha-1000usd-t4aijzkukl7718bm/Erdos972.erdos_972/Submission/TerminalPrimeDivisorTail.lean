import Submission.PrimeSmoothDivisorEstimate
import Submission.PrimeRowLogSharpness

/-! Exact signed terminal divisor tails. The terminal range reduces to
Möbius weights on the actual Beatty outputs; no cancellation is asserted. -/
namespace Erdos972TerminalPrimeDivisorTail

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Erdos972PrimeSmoothDivisorEstimate Erdos972PrimeLeastFactorScales
open Erdos972PrimeRoughOutputs Erdos972PrimePowerError Erdos972SmoothDivisorTail
open Erdos972ExponentialSum Erdos972PrimeRowLogSharpness

set_option autoImplicit false
set_option maxHeartbeats 1500000

lemma large_divisor_eq_self {D n d : ℕ} (hn : n ≤ 2*D)
    (hd : D < d) (hdn : d ∣ n) (hn0 : 0 < n) : d = n := by
  obtain ⟨k, hk⟩ := hdn
  have hd0 : 0 < d := (Nat.zero_le D).trans_lt hd
  have hk0 : 0 < k := by nlinarith only [hk, hn0]
  have hk1 : k = 1 := by
    by_contra hh
    have hk2 : 2 ≤ k := by omega
    nlinarith only [hn, hd, hk, hk2]
  simpa only [hk1, mul_one] using hk.symm

/-- Above half the size of an integer, its only possible divisor is itself. -/
theorem expTail_terminal (t : ℝ) {D n : ℕ} (hn : n ≤ 2*D) :
    expTail t D n = if D < n then dampedCoefficient t n else 0 := by
  classical
  rw [expTail_eq]
  by_cases hn0 : n = 0
  · simp [hn0]
  by_cases hDn : D < n
  · rw [if_pos hDn, sum_eq_single n]
    · intro d hd hdn
      obtain ⟨hdiv, hdD⟩ := mem_filter.mp hd
      exact (hdn (large_divisor_eq_self hn hdD (Nat.mem_divisors.mp hdiv).1
        (Nat.pos_of_ne_zero hn0))).elim
    · intro hnot
      exact (hnot (mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨dvd_refl _, hn0⟩, hDn⟩)).elim
  · rw [if_neg hDn]
    apply sum_eq_zero
    intro d hd
    obtain ⟨hdiv, hdD⟩ := mem_filter.mp hd
    have hdn := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (Nat.mem_divisors.mp hdiv).1
    omega

noncomputable def terminalMoebiusPrimeSum (t α : ℝ) (D N : ℕ) : ℝ :=
  ∑ p ∈ Ioc 0 N, if D < floorMul α p then
    primeWeight p*(μ (floorMul α p):ℝ)*damping t (floorMul α p) else 0

/-- The entire terminal tail is an actual signed prime-input/Möbius-output
correlation. Scalar Möbius sums cannot be substituted for this expression. -/
theorem prime_exp_terminal_tail {α : ℝ} (hα : 1 ≤ α) (t : ℝ) {D N : ℕ}
    (hND : floorMul α N ≤ 2*D) :
    primeExpSum t α N-primeTruncatedExpSum t α D N = terminalMoebiusPrimeSum t α D N := by
  have he : primeExpSum t α N-primeTruncatedExpSum t α D N =
      ∑ p ∈ Ioc 0 N, primeWeight p*expTail t D (floorMul α p) := by
    simp only [primeExpSum, primeTruncatedExpSum, expTail, mul_sub, sum_sub_distrib]
  rw [he, terminalMoebiusPrimeSum]
  apply sum_congr rfl
  intro p hp
  rw [expTail_terminal t (((floorMul_strictMono hα).monotone (mem_Ioc.mp hp).2).trans hND)]
  split_ifs <;> simp only [dampedCoefficient, damping, mul_zero, mul_assoc]

/-- A terminal-range absolute bound with no divisor-cardinality or
logarithmic factor. Dividing by t to recover the smoothed Mangoldt sum
still costs 1/t. -/
theorem terminalMoebiusPrimeSum_bound {t : ℝ} (ht : 0 ≤ t) (α : ℝ) (D N : ℕ) :
    |terminalMoebiusPrimeSum t α D N| ≤ damping t D*Chebyshev.theta N := by
  unfold terminalMoebiusPrimeSum
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ p ∈ Ioc 0 N, damping t D*primeWeight p := by
      apply sum_le_sum
      intro p hp
      split_ifs with hD
      · rw [abs_mul, abs_mul, abs_of_nonneg (primeWeight_nonneg p),
          abs_of_pos (damping_pos _ _)]
        have hmu : |(μ (floorMul α p):ℝ)| ≤ 1 := by
          exact_mod_cast abs_moebius_le_one (n := floorMul α p)
        have hd : damping t (floorMul α p) ≤ damping t D := by
          apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonpos_left (monotone_log_natCast hD.le) (neg_nonpos.mpr ht)
        have hh := mul_le_mul_of_nonneg_left
          (mul_le_mul hmu hd (damping_pos _ _).le zero_le_one) (primeWeight_nonneg p)
        nlinarith only [hh]
      · rw [abs_zero]
        exact mul_nonneg (damping_pos _ _).le (primeWeight_nonneg p)
    _ = _ := by rw [← mul_sum, primeWeight_sum_theta]

/-- A corresponding exact finite identity for the genuine prime-input
smoothed Mangoldt sum. -/
theorem prime_smooth_terminal_identity {α t : ℝ} (hα : 1 ≤ α) (ht : 0 < t) {D N : ℕ}
    (hND : floorMul α N ≤ 2*D) :
    t*mixedPrimeSmooth t α N = primeTruncatedExpSum t α D N+terminalMoebiusPrimeSum t α D N := by
  have hh := prime_exp_terminal_tail hα t hND
  rw [primeExpSum_eq hα ht] at hh
  linarith only [hh]

#print axioms expTail_terminal
#print axioms prime_exp_terminal_tail
#print axioms terminalMoebiusPrimeSum_bound
#print axioms prime_smooth_terminal_identity

end Erdos972TerminalPrimeDivisorTail
