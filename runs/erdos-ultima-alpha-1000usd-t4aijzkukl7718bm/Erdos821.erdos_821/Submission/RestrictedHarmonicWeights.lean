import Submission.IntervalPrimeWeights

/-! # Harmonic averages for a restricted prime pool -/
open Nat Finset
open scoped Classical BigOperators
namespace Erdos821.Sieve

lemma harmonic_average_restricted_prime_product (A : ℕ) (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (w : ℕ → ℝ) (hw : ∀ p ∈ Q, 0 ≤ w p) :
    (∑ n ∈ Icc 1 A, (∏ p ∈ Q with p ∣ n, (1+w p))/(n : ℝ)) ≤
      (harmonic A : ℝ)*(∏ p ∈ Q, (1+w p/(p : ℝ))) := by
  have hweight (S : Finset ℕ) (hS : S ∈ Q.powerset) : 0 ≤ ∏ p ∈ S, w p :=
    Finset.prod_nonneg (fun p hp => hw p (Finset.mem_powerset.mp hS hp))
  calc
    (∑ n ∈ Finset.Icc 1 A, (∏ p ∈ Q with p ∣ n, (1 + w p)) / (n : ℝ)) =
        ∑ n ∈ Finset.Icc 1 A, ∑ S ∈ Q.powerset,
          (∏ p ∈ S, w p) * (if (∏ p ∈ S, p) ∣ n then (n : ℝ)⁻¹ else 0) := by
      apply Finset.sum_congr rfl
      intro n _hn
      rw [prime_product_expansion Q hQ w n, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro S hS
      split_ifs <;> simp [div_eq_mul_inv]
    _ = ∑ S ∈ Q.powerset, (∏ p ∈ S, w p) *
        ∑ n ∈ Finset.Icc 1 A with (∏ p ∈ S, p) ∣ n, (n : ℝ)⁻¹ := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_filter, Finset.mul_sum]
    _ ≤ ∑ S ∈ Q.powerset, (∏ p ∈ S, w p) *
        (((∏ p ∈ S, p : ℕ) : ℝ)⁻¹ * (harmonic A : ℝ)) := by
      apply Finset.sum_le_sum
      intro S hS
      apply mul_le_mul_of_nonneg_left ?_ (hweight S hS)
      exact sum_inv_multiples_le_harmonic A _
        (Finset.prod_pos (fun p hp => (hQ p (Finset.mem_powerset.mp hS hp)).pos))
    _ = (harmonic A : ℝ) * ∑ S ∈ Q.powerset, ∏ p ∈ S, w p / (p : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S hS
      rw [Finset.prod_div_distrib, Nat.cast_prod]
      ring
    _ = _ := by rw [← Finset.prod_one_add]

end Erdos821.Sieve
