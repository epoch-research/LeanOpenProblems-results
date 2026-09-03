import Submission.HarmonicDivisorLower

/-!
# A uniform-in-order comparison for truncated divisor moments

Retaining a rectangle in the convolution gives a lower bound for the
cofactor harmonic moment, uniformly in its order. This can check whether
the current lower/upper estimates overlap even when the order grows.
It is not a disproof of Erdős 821, nor an obstruction to other estimates.
-/

open Nat Filter ArithmeticFunction
open scoped Classical BigOperators ArithmeticFunction.zeta Topology

namespace Erdos821.HigherDivisors

set_option maxHeartbeats 2000000

/-- A rectangle entirely below the hyperbola contributes to the next
harmonic divisor moment. The order is arbitrary, not fixed asymptotically. -/
theorem harmonicMoment_rectangle_lower (k Q B K : ℕ)
    (hQ : 1 ≤ Q) (hQB : Q*B ≤ K) :
    harmonicMoment k Q * harmonicMoment 1 B ≤ harmonicMoment (k+1) K := by
  have hBK : B ≤ K := (Nat.le_mul_of_pos_left B hQ).trans hQB
  have hbase : harmonicMoment 1 B = ∑ m ∈ Finset.Icc 1 B, (m : ℝ)⁻¹ := by
    unfold harmonicMoment
    apply Finset.sum_congr rfl
    intro m hm
    simp only [tau, pow_one, zeta_apply_ne (by
      have := (Finset.mem_Icc.mp hm).1; omega : m ≠ 0), Nat.cast_one, one_div]
  rw [hbase, Finset.mul_sum, harmonicMoment_succ]
  calc
    _ ≤ ∑ m ∈ Finset.Icc 1 B, harmonicMoment k (K/m)/(m : ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      have hm0 : 0 < m := (Finset.mem_Icc.mp hm).1
      have hQm : Q ≤ K/m := (Nat.le_div_iff_mul_le hm0).mpr
        ((Nat.mul_le_mul_left Q (Finset.mem_Icc.mp hm).2).trans hQB)
      simpa only [div_eq_mul_inv] using div_le_div_of_nonneg_right
        (harmonicMoment_mono k hQm) (Nat.cast_nonneg m)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc_right hBK)
      (fun m _ _ => div_nonneg (harmonicMoment_nonneg k (K/m)) (Nat.cast_nonneg m))

/-- A logarithmic factor is gained from the unused cutoff interval. -/
theorem harmonicMoment_log_rectangle_lower (k Q B K : ℕ)
    (hQ : 1 ≤ Q) (hB : 1 ≤ B) (hQB : Q*B ≤ K) :
    harmonicMoment k Q * Real.log (B+1 : ℝ) ≤ harmonicMoment (k+1) K := by
  have h := harmonicMoment_factorial_lower 1 B hB
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one] at h
  exact (mul_le_mul_of_nonneg_left h (harmonicMoment_nonneg k Q)).trans
    (harmonicMoment_rectangle_lower k Q B K hQ hQB)

/-- Under an explicit numerical condition, even the idealized truncated
prime-moment main term is at most the rough sieve's main upper expression.
This is a comparison of the estimates, not a lower bound for rough primes. -/
theorem truncated_main_le_rough_sieve_main (k Q B K X J : ℕ) (L : ℝ)
    (hQ : 1 ≤ Q) (hB : 1 ≤ B) (hQB : Q*B ≤ K) (hL : 0 < L) (hJ : 0 < J)
    (hscale : ((J : ℝ)*Real.log 2)^2 ≤
      16*(k+1 : ℝ)*eulerCost (k+1)*L*Real.log (B+1 : ℝ)) :
    (X : ℝ)/L * harmonicMoment k Q ≤
      (k+1 : ℝ)*(16*(X : ℝ)/((J : ℝ)*Real.log 2)^2)*
        (eulerCost (k+1)*harmonicMoment (k+1) K) := by
  have hD : 0 < ((J : ℝ)*Real.log 2)^2 := by
    have : (0 : ℝ) < J := by exact_mod_cast hJ
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hH := harmonicMoment_log_rectangle_lower k Q B K hQ hB hQB
  have hC : 0 ≤ 16*(k+1 : ℝ)*eulerCost (k+1)*L := by
    positivity [eulerCost_pos (k+1)]
  have hprod := mul_le_mul_of_nonneg_left hH hC
  have hscale' := mul_le_mul_of_nonneg_right hscale (harmonicMoment_nonneg k Q)
  have hkey : ((J : ℝ)*Real.log 2)^2 * harmonicMoment k Q ≤
      16*(k+1 : ℝ)*eulerCost (k+1)*L*harmonicMoment (k+1) K := by
    nlinarith only [hprod, hscale']
  have hx := mul_le_mul_of_nonneg_left hkey (Nat.cast_nonneg X)
  apply (mul_le_mul_iff_left₀ (mul_pos hL hD)).mp
  convert hx using 1 <;> field_simp [hL.ne', hD.ne']

/-- If a positive logarithmic gap remains between the two cutoffs,
increasing the order eventually makes the current two main expressions
overlap. All inequalities are finite and uniform in the order. -/
theorem truncated_main_le_rough_of_large_order (k Q B K X J : ℕ) (L A b : ℝ)
    (hQ : 1 ≤ Q) (hB : 1 ≤ B) (hQB : Q*B ≤ K)
    (hL : 0 < L) (hJ : 0 < J) (hb : 0 < b)
    (hJscale : (J : ℝ)*Real.log 2 ≤ A*L)
    (hBscale : b*L ≤ Real.log (B+1 : ℝ))
    (horder : A^2 ≤ 16*(k+1 : ℝ)*b) :
    (X : ℝ)/L * harmonicMoment k Q ≤
      (k+1 : ℝ)*(16*(X : ℝ)/((J : ℝ)*Real.log 2)^2)*
        (eulerCost (k+1)*harmonicMoment (k+1) K) := by
  apply truncated_main_le_rough_sieve_main k Q B K X J L hQ hB hQB hL hJ
  have hD : 0 ≤ (J : ℝ)*Real.log 2 := by
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  have hsquare : ((J : ℝ)*Real.log 2)^2 ≤ (A*L)^2 :=
    pow_le_pow_left₀ hD hJscale 2
  have h1 := mul_le_mul_of_nonneg_right horder (sq_nonneg L)
  have h2 := mul_le_mul_of_nonneg_left hBscale
    (show 0 ≤ 16*(k+1 : ℝ)*L by positivity)
  have h3 := mul_le_mul_of_nonneg_right (eulerCost_ge_one (k+1))
    (show 0 ≤ 16*(k+1 : ℝ)*L*Real.log (B+1 : ℝ) by
      have : 0 ≤ Real.log (B+1 : ℝ) := le_trans (by positivity) hBscale
      positivity)
  nlinarith only [hsquare, h1, h2, h3]

end Erdos821.HigherDivisors
