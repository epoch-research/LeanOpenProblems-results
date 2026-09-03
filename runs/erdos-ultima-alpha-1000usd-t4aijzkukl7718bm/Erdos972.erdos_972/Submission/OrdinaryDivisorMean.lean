import Submission.OrdinaryRotationMean
import Submission.DampedSingleMean

/-! All-cutoff fixed-divisor row means for irrational slopes and their
finite-polynomial consequences. Divisor indices are fixed before the input
cutoff tends to infinity. -/
namespace Erdos972OrdinaryDivisorMean

open Finset Filter
open scoped Topology
open Erdos972OrdinaryRotationMean Erdos972RationalRotationCount
open Erdos972DivisorPairCount Erdos972DivisorCovariance Erdos972DampedSingleMean
open Erdos972SmoothDivisorTail Erdos972PrimePowerError

lemma divisorRow_mean {α : ℝ} (hα : 0 ≤ α) (hI : Irrational α)
    {d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    Tendsto (fun K : ℕ => ((divisorRow α K d e).card : ℝ)/(K : ℝ)) atTop (𝓝 (1/(e : ℝ))) := by
  by_cases he1 : e = 1
  · subst e
    have hh : Tendsto (fun K : ℕ => (1 : ℝ)) atTop (𝓝 (1 : ℝ)) := tendsto_const_nhds
    simp only [Nat.cast_one, div_one]
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with K hK
    have hK0 : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hK)
    simp [divisorRow, hK0]
  have hirr := (hI.mul_natCast hd.ne').div_natCast he.ne'
  have heR : (1 : ℝ) < e := by exact_mod_cast (show 1 < e by omega)
  have hh := rotationInterval_mean hirr (by positivity : (0 : ℝ) < 1/(e : ℝ))
    ((div_lt_one (by positivity)).mpr heR)
  simpa only [← divisorRow_eq_rotationInterval hα _ _ _ he] using hh

/-- Every fixed pair of divisors has the product local density at every
sufficiently large input cutoff, not only on selected rational scales. -/
theorem divisorPairs_mean {α : ℝ} (hα : 0 ≤ α) (hI : Irrational α)
    {d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    Tendsto (fun N : ℕ => ((divisorPairs α N d e).card : ℝ)/(N : ℝ))
      atTop (𝓝 (1/((d : ℝ)*e))) := by
  have hdiv : Tendsto (fun N : ℕ => N/d) atTop atTop := le_of_eq (map_div_atTop_eq_nat d hd)
  have hK : Tendsto (fun N : ℕ => N/d+1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp hdiv
  have hrow := (divisorRow_mean hα hI hd he).comp hK
  have hinv := tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
  have hratio : Tendsto (fun N : ℕ => ((N/d+1 : ℕ) : ℝ)/(N : ℝ)) atTop (𝓝 (1/(d : ℝ))) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_div, add_zero] using (nat_div_ratio_tendsto d).add hinv
  have hh := (hrow.mul hratio).sub hinv
  have hlim : (1/(e : ℝ))*(1/(d : ℝ))-0 = 1/((d : ℝ)*e) := by ring
  rw [hlim] at hh
  apply hh.congr'
  filter_upwards with N
  simp only [Function.comp_apply]
  have hKN : ((N/d+1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero (N/d))
  have hc : ((divisorRow α (N/d+1) d e).card : ℝ) = (divisorPairs α N d e).card+1 := by
    exact_mod_cast (divisorPairs_card_add_one α N d e hd).symm
  rw [hc]
  field_simp
  ring

lemma truncated_correlation_polynomial {α : ℝ} (hα : 1 ≤ α) (t : ℝ) (D N : ℕ) :
    truncatedExpCorrelation t α D N =
      ∑ n ∈ Ioc 0 N, divisorPolynomial D (dampedCoefficient t) n *
        divisorPolynomial D (dampedCoefficient t) (floorMul α n) := by
  apply sum_congr rfl
  intro n hn
  rw [truncatedExpSum_eq_polynomial t D (mem_Ioc.mp hn).1.ne',
    truncatedExpSum_eq_polynomial t D (floorMul_pos hα (mem_Ioc.mp hn).1).ne']

lemma divisorMean_product_expansion (D : ℕ) (a : ℕ → ℝ) :
    (divisorMean D a)^2 =
      ∑ d ∈ Ioc 0 D, ∑ e ∈ Ioc 0 D, a d*a e*(1/((d : ℝ)*e)) := by
  rw [divisorMean, pow_two, sum_mul_sum]
  apply sum_congr rfl
  intro d _
  apply sum_congr rfl
  intro e _
  ring

/-- Fixed-cutoff smoothed correlations have the product mean along all
natural input cutoffs. No limit of the divisor cutoff with N is taken. -/
theorem truncated_correlation_mean {α : ℝ} (hα : 1 ≤ α) (hI : Irrational α)
    (t : ℝ) (D : ℕ) :
    Tendsto (fun N : ℕ => truncatedExpCorrelation t α D N/(N : ℝ)) atTop
      (𝓝 ((divisorMean D (dampedCoefficient t))^2)) := by
  have hh := tendsto_finset_sum (Ioc 0 D) (fun d hd =>
    tendsto_finset_sum (Ioc 0 D) (fun e he =>
      (divisorPairs_mean (show 0 ≤ α by linarith) hI (mem_Ioc.mp hd).1 (mem_Ioc.mp he).1).const_mul
        (dampedCoefficient t d*dampedCoefficient t e)))
  rw [← divisorMean_product_expansion] at hh
  convert hh using 1
  funext N
  rw [truncated_correlation_polynomial hα, polynomial_pair_expansion]
  simp only [sum_div, mul_div_assoc]

#print axioms divisorPairs_mean
#print axioms truncated_correlation_mean

end Erdos972OrdinaryDivisorMean
