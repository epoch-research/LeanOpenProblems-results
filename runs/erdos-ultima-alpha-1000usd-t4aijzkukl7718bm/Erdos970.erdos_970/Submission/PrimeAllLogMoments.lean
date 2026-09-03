import Submission.CumulativeVariation
import Submission.PrimeSharpLogMoments

/-! Sharp leading coefficients for all positive higher logarithmic prime
moments, from the elementary weighted Mertens estimate and finite layer cake. -/
namespace Erdos970.WeightedMertens
open Finset Real Erdos970.FiniteSelberg

/-- Uniform sharp leading coefficient for any logarithmic moment of degree
at least two. The bound does not use the prime number theorem. -/
theorem prime_log_moment (R : ℕ) (hR : 0 < R) (n : ℕ) :
    |(∑ p ∈ (R + 1).primesBelow, log (p : ℝ) ^ (n + 2) / p) -
      log (R : ℝ) ^ (n + 2) / ((n : ℝ) + 2)| ≤
      2 * sharpMomentError * log (R : ℝ) ^ (n + 1) := by
  let P := (R + 1).primesBelow
  have ha (p : P) : 0 ≤ log (p.val : ℝ) ∧ log (p.val : ℝ) ≤ log R := by
    obtain ⟨hpp, hpR⟩ := mem_primes.mp p.property
    exact ⟨log_natCast_nonneg _, log_le_log (by exact_mod_cast hpp.pos) (by exact_mod_cast hpR)⟩
  have htotal : |(∑ p : P, log (p.val : ℝ) / p.val) - log (R : ℝ)| ≤ sharpMomentError := by
    have hs : (∑ p : P, log (p.val : ℝ) / p.val) = primeSum R :=
      sum_coe_sort P (fun p : ℕ => log (p : ℝ) / p)
    rw [hs]
    exact (abs_primeSum_sub_log R hR).trans (by unfold sharpMomentError; linarith)
  have hh := cumulative_power_moment (fun p : P => log (p.val : ℝ) / p.val)
    (fun p : P => log (p.val : ℝ)) (log R) sharpMomentError (log_natCast_nonneg R)
    ha htotal (fun t ht => by
      rw [initialPrimeCumulative_eq]
      exact initialPrimeCumulative_error R hR t ht.1 ht.2) n
  have he : (∑ p : P, (log (p.val : ℝ) / p.val) * log (p.val : ℝ) ^ (n + 1)) =
      ∑ p ∈ P, log (p : ℝ) ^ (n + 2) / p := by
    rw [sum_coe_sort P (fun p : ℕ => (log (p : ℝ) / p) * log (p : ℝ) ^ (n + 1))]
    apply sum_congr rfl
    intro p hp
    rw [show n + 2 = (n + 1) + 1 from by omega, pow_succ]
    ring
  rwa [he] at hh

lemma prime_fifth_log_moment (R : ℕ) (hR : 0 < R) :
    |(∑ p ∈ (R + 1).primesBelow, log (p : ℝ) ^ 5 / p) - log (R : ℝ) ^ 5 / 5| ≤
      2 * sharpMomentError * log (R : ℝ) ^ 4 := by
  convert prime_log_moment R hR 3 using 1 <;> norm_num

#print axioms prime_log_moment
#print axioms prime_fifth_log_moment
end Erdos970.WeightedMertens
