import Submission.QuarterTrackerBridge
import Submission.QuarterLaplaceBounds

/-! Dyadic Laplace submultiplicativity fails even at the fixed parameter
log 2. All counts are for the actual five-prime residue-phase model. This
is not a disproof of the Jacobsthal conjecture or a claim about every
sufficiently small positive parameter. -/
namespace Erdos970.GapAverages.QuarterExample
open Real

lemma scaled_25236 : (2 : ℝ)^11887 * countLaplace primes (log 2) 25236 =
    (33897666 : ℝ)/100947 := by
  have hh := scaled_laplace 25236 11887 (fun a _ => (count_bounds a).1)
  rw [weighted_values.1] at hh
  exact hh

lemma scaled_50472 : (2 : ℝ)^23774 * countLaplace primes (log 2) 50472 =
    (13280119881 : ℝ)/100947 := by
  have hh := scaled_laplace 50472 23774 (fun a _ => (count_bounds a).2)
  rw [weighted_values.2] at hh
  exact hh

lemma scale_square : ((2 : ℝ)^11887)^2 = (2 : ℝ)^23774 := by
  rw [← pow_mul]

/-- Exact failure at log 2; no numerical approximation to exp or log is used. -/
theorem dyadic_log_two_failure :
    countLaplace primes (log 2) 25236 ^ 2 < countLaplace primes (log 2) (2*25236) := by
  have hscale : (0 : ℝ) < ((2 : ℝ)^11887)^2 :=
    pow_pos (pow_pos (by norm_num) _) _
  apply (mul_lt_mul_iff_left₀ hscale).mp
  calc
    countLaplace primes (log 2) 25236^2 * ((2 : ℝ)^11887)^2 =
        ((2 : ℝ)^11887 * countLaplace primes (log 2) 25236)^2 := by rw [mul_pow, mul_comm]
    _ = ((33897666 : ℝ)/100947)^2 := by rw [scaled_25236]
    _ < (13280119881 : ℝ)/100947 := by norm_num
    _ = countLaplace primes (log 2) (2*25236) * ((2 : ℝ)^11887)^2 := by
      rw [scale_square, mul_comm]
      exact scaled_50472.symm

/-- Thus the dyadic inequality is not valid uniformly at this fixed positive
parameter. Smaller fixed parameters remain a different unproved question. -/
theorem not_dyadic_at_log_two :
    ¬∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → ∀ m : ℕ,
      countLaplace P (log 2) (2*m) ≤ countLaplace P (log 2) m ^ 2 := by
  intro h
  exact dyadic_log_two_failure.not_ge (h primes primes_prime 25236)

#print axioms scaled_25236
#print axioms scaled_50472
#print axioms dyadic_log_two_failure
#print axioms not_dyadic_at_log_two
end Erdos970.GapAverages.QuarterExample
