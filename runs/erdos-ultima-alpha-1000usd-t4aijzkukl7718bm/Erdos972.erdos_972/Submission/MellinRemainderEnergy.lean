import Submission.MellinMeanSquare

/-!
Energy bounds for the complete Vaughan remainder. These retain its actual
coefficients and do not claim signed correlation cancellation.
-/
namespace Erdos972MellinRemainderEnergy

open Finset MeasureTheory ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta
open Erdos972Vaughan Erdos972DoubleVaughan Erdos972MellinDivisorCoefficient
open Erdos972MellinMeanSquare

set_option maxHeartbeats 1000000

lemma remainder_abs_bound (U V n : ℕ) :
    |typeIIPart U V n| ≤ (n.divisors.card : ℝ)*Real.log n := by
  unfold typeIIPart
  rw [mul_comm _ (tail Λ V), ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun d e => tail Λ V d * (tail (μ : ArithmeticFunction ℝ) U * ζ) e)]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ d ∈ n.divisors, (n.divisors.card : ℝ)*Λ d := by
      apply sum_le_sum
      intro d hd
      have hdn := Nat.mem_divisors.mp hd
      have hc : ((n/d).divisors.card : ℝ) ≤ n.divisors.card := Nat.cast_le.mpr
        (card_le_card (Nat.divisors_subset_of_dvd hdn.2 (Nat.div_dvd_of_dvd hdn.1)))
      have ha := (abs_typeII_coefficient_le_card_divisors U (n/d)).trans hc
      rw [abs_mul, abs_of_nonneg (tail_vonMangoldt_nonneg V d)]
      have hm := mul_le_mul (tail_vonMangoldt_le V d) ha (abs_nonneg _)
        (vonMangoldt_nonneg (n := d))
      exact hm.trans_eq (by ring)
    _ = _ := by rw [← mul_sum, vonMangoldt_sum]

lemma remainder_energy {N : ℕ} (s : Finset ℕ) (hs : s ⊆ Ioc 0 N) (U V : ℕ) :
    energy s (fun n => (typeIIPart U V n : ℂ)) ≤
      (Real.log N)^2*((N : ℝ)*(1+Real.log N)^3) := by
  have hp (n : ℕ) (hn : n ∈ Ioc 0 N) :
      ‖(typeIIPart U V n : ℂ)‖^2 ≤ (Real.log N)^2*(n.divisors.card : ℝ)^2 := by
    have hl : Real.log n ≤ Real.log N := Real.log_le_log
      (Nat.cast_pos.mpr (mem_Ioc.mp hn).1) (Nat.cast_le.mpr (mem_Ioc.mp hn).2)
    have hh := (remainder_abs_bound U V n).trans
      (mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg _))
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (pow_le_pow_left₀ (abs_nonneg _) hh 2).trans_eq (by ring)
  apply (sum_le_sum (fun n hn => hp n (hs hn))).trans
  apply (sum_le_sum_of_subset_of_nonneg hs (fun n hn hnot => by positivity)).trans
  rw [← mul_sum]
  exact mul_le_mul_of_nonneg_left (Erdos972DivisorEnergy.sum_card_divisors_square_le_log N) (sq_nonneg _)

/-- An unrestricted-frequency upper bound, with the logarithmic energy loss
explicit rather than hidden in a claimed little-o estimate. -/
theorem remainder_mellin_mean_square {N : ℕ} (s : Finset ℕ) (hs : s ⊆ Ioc 0 N)
    (U V : ℕ) {A B : ℝ} (hAB : A ≤ B) :
    (∫ t in A..B, ‖∑ n ∈ s, (typeIIPart U V n : ℂ)*mellinPhase t n‖^2) ≤
      (B-A+4*(N : ℝ)*(1+Real.log N))*
        ((Real.log N)^2*((N : ℝ)*(1+Real.log N)^3)) := by
  have hh := mellin_mean_square s hs (fun n => (typeIIPart U V n : ℂ)) A B
  have he := remainder_energy s hs U V
  have hC : 0 ≤ B-A+4*(N : ℝ)*(1+Real.log N) := by
    have hlog := Real.log_natCast_nonneg N
    have hBA := sub_nonneg.mpr hAB
    positivity
  have hb := mul_le_mul_of_nonneg_left he hC
  have hi := (abs_le.mp hh).2
  nlinarith only [hi, hb]

#print axioms remainder_abs_bound
#print axioms remainder_energy
#print axioms remainder_mellin_mean_square

end Erdos972MellinRemainderEnergy
