import Submission.DampedCoefficients

/-! Fixed-degree endpoint terms in the damping expansion have zero mean. -/
namespace Erdos371
open Finset Filter
open scoped Topology

lemma primeFactors_card_log_bound (n : ℕ) (hn : 0 < n) :
    (n.primeFactors.card : ℝ) ≤ Real.log n/Real.log 2 := by
  have hp : 2^n.primeFactors.card ≤ n := by
    apply (pow_card_le_prod n.primeFactors id 2
      (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)).trans
    exact Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)
  have hR : (2 : ℝ)^n.primeFactors.card ≤ n := by exact_mod_cast hp
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ)^n.primeFactors.card) hR
  rw [Real.log_pow] at hl
  exact (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hl

lemma primeFactors_choose_endpoint_zero (k : ℕ) :
    Tendsto (fun N : ℕ => (N.primeFactors.card.choose k : ℝ)/N) atTop (𝓝 0) := by
  have ht := ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 k (by norm_num)).comp
    tendsto_natCast_atTop_atTop).div_const ((Real.log 2)^k)
  simp only [Function.comp_def,one_mul,add_zero,zero_div] at ht
  apply squeeze_zero' (Eventually.of_forall (fun N => by positivity)) _ ht
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hC : (N.primeFactors.card.choose k : ℝ) ≤ (N.primeFactors.card : ℝ)^k := by
    exact_mod_cast Nat.choose_le_pow N.primeFactors.card k
  have hB := pow_le_pow_left₀ (Nat.cast_nonneg N.primeFactors.card) (primeFactors_card_log_bound N hN) k
  have hh := div_le_div_of_nonneg_right (hC.trans hB) (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  convert hh using 1; ring

lemma primeFactors_choose_succ_endpoint_zero (k : ℕ) :
    Tendsto (fun N : ℕ => ((N+1).primeFactors.card.choose k : ℝ)/N) atTop (𝓝 0) := by
  have ht := (primeFactors_choose_endpoint_zero k).comp (tendsto_add_atTop_nat 1)
  have hr : Tendsto (fun N : ℕ => ((N : ℝ)+1)/N) atTop (𝓝 1) := by
    have hh := tendsto_one_div_atTop_nhds_zero_nat.const_add (1 : ℝ)
    simp only [add_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
  have hh := ht.mul hr
  simp only [zero_mul,Function.comp_def] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  simp only [Nat.cast_add,Nat.cast_one]
  have hn : (N : ℝ)+1 ≠ 0 := by positivity
  field_simp

lemma dampedFactorSign_linear_mean_zero :
    Tendsto (fun N : ℕ => (∑ n ∈ range N,
      dampedCoefficient 1 (fun p => if p ∣ n+2 then 1 else -1)
        ((n+1)*(n+2)).primeFactors)/N) atTop (𝓝 0) := by
  simp_rw [dampedFactorSign_linear_prefix]
  simpa only [Nat.choose_one_right] using primeFactors_choose_succ_endpoint_zero 1

#print axioms primeFactors_choose_endpoint_zero
#print axioms primeFactors_choose_succ_endpoint_zero
end Erdos371
