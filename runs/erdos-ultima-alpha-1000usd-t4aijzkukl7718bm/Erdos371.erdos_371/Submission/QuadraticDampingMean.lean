import Submission.QuadraticPrimeSplit
import Submission.PrimeFactorCardEndpoint

/-! What quadratic damping cancellation would require. Short-prime-product
and endpoint errors vanish; a signed large-pair multiplicity remains. -/
namespace Erdos371
open Finset Filter
open scoped Topology

noncomputable def quadraticFactorSign (n : ℕ) : ℝ :=
  dampedCoefficient 2 (fun p => if p ∣ n+1 then 1 else -1) (n*(n+1)).primeFactors

lemma quadraticFactorSign_prefix (N : ℕ) :
    (∑ n ∈ range N, quadraticFactorSign (n+1)) =
      -((N+1).primeFactors.card.choose 2 : ℝ)+∑ n ∈ range N, crossPrimeSkew (n+1) := by
  have he (n : ℕ) : quadraticFactorSign (n+1) =
      ((n+1).primeFactors.card.choose 2 : ℝ)-(n+2).primeFactors.card.choose 2+crossPrimeSkew (n+1) := by
    exact dampedFactorSign_quadratic_coefficient (n+1) (by omega)
  simp_rw [he]
  rw [sum_add_distrib]
  congr 1
  induction N with
  | zero => simp
  | succ N ih => rw [sum_range_succ,ih]; ring

lemma crossPrimeSkew_shifted_prefix (N : ℕ) :
    (∑ n ∈ range N, crossPrimeSkew (n+1)) =
      (∑ n ∈ range N, shortPrimePairSkew (N+1) (n+1))+
      ∑ n ∈ range N, (largeCrossPrimePairs (N+1) (n+1)).card*factorSign (n+1) := by
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro n hn
  have hN : n+1+1 ≤ N+1 := by have := mem_range.mp hn; omega
  rw [crossPrimeSkew_split (N+1) (n+1) (by omega) hN,
    largeCrossPrimePairSkew_eq_of_pos (N+1) (n+1) (by omega) hN]

/-- An unconditional signed error estimate, retaining the variable
large-product multiplicity in the unevaluated mean. -/
theorem quadraticFactorSign_mean_large_pair_error :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, quadraticFactorSign (n+1))/N-
      (∑ n ∈ range N, (largeCrossPrimePairs (N+1) (n+1)).card*factorSign (n+1))/N)
      atTop (𝓝 0) := by
  have ht := (primeFactors_choose_succ_endpoint_zero 2).neg.add shortPrimePairSkew_succ_mean_zero
  simp only [neg_zero,zero_add] at ht
  convert ht using 1
  ext N
  rw [quadraticFactorSign_prefix,crossPrimeSkew_shifted_prefix]
  ring

#print axioms quadraticFactorSign_prefix
#print axioms quadraticFactorSign_mean_large_pair_error
end Erdos371
