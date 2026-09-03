import Submission.TruncatedMomentModels

/-!
# A finite moment-bootstrap audit for the smooth product moduli

At large scales, the exact reciprocal-totient main terms have a normalized
nonnegative model with any prescribed finite initial segment of moments and
no tail beyond that segment. This is an abstract moment model, not a prime
sequence and not a counterexample to Erdős 821.
-/

open Nat Finset Filter
open scoped Classical BigOperators

namespace Erdos821

open AnalyticSieve

set_option maxHeartbeats 2000000

lemma blockPrimeDivisors_eq_primeFactors_of_product {r m d : ℕ}
    (hd : d ∈ primeProductModuli r m) : blockPrimeDivisors m d = d.primeFactors := by
  ext q
  constructor
  · intro hq
    obtain ⟨hqB, hqd⟩ := mem_filter.mp hq
    exact (mem_geometricBlockPrimes.mp hqB).1.mem_primeFactors hqd (primeProductModuli_properties hd).1.ne'
  · intro hq
    exact mem_filter.mpr ⟨prime_product_prime_factor_mem hd hq, Nat.dvd_of_mem_primeFactors hq⟩

lemma singleton_product_divisor_count {r m d : ℕ} (hd : d ∈ primeProductModuli r m) :
    ((primeProductModuli 1 m).filter (fun c => c ∣ d)).card = r := by
  rw [prime_product_divisor_count_eq_choose, blockPrimeDivisors_eq_primeFactors_of_product hd,
    Nat.choose_one_right, (primeProductModuli_properties hd).2.2.1]

lemma primeProductReciprocalMass_zero (m : ℕ) : primeProductReciprocalMass 0 m = 1 := by
  simp [primeProductReciprocalMass, primeProductModuli]

/-- The elementary-symmetric main terms satisfy a factorial moment ratio
bound, with the first reciprocal mass as the ratio parameter. -/
theorem primeProductReciprocalMass_succ_ratio (r m : ℕ) :
    ((r + 1 : ℕ) : ℝ) * primeProductReciprocalMass (r + 1) m ≤
      primeProductReciprocalMass 1 m * primeProductReciprocalMass r m := by
  have hsum : (∑ c ∈ primeProductModuli 1 m,
      ∑ d ∈ (primeProductModuli (r + 1) m).filter (fun d => c ∣ d), (d.totient : ℝ)⁻¹) =
      ((r + 1 : ℕ) : ℝ) * primeProductReciprocalMass (r + 1) m := by
    simp_rw [sum_filter]
    rw [sum_comm]
    unfold primeProductReciprocalMass
    rw [mul_sum]
    apply sum_congr rfl
    intro d hd
    rw [← sum_filter, sum_const, nsmul_eq_mul, singleton_product_divisor_count hd]
  rw [← hsum]
  calc
    _ ≤ ∑ c ∈ primeProductModuli 1 m, (c.totient : ℝ)⁻¹ * primeProductReciprocalMass r m := by
      apply sum_le_sum
      intro c hc
      simpa only [Nat.add_sub_cancel] using prime_product_conductor_completion_le (by omega : 1 ≤ r + 1) hc
    _ = _ := by rw [← sum_mul]; rfl

lemma primeProductReciprocalMass_one_le_one (m : ℕ) (hm : 2^64 ≤ m) :
    primeProductReciprocalMass 1 m ≤ 1 := by
  have hm1 : 1 ≤ m := (Nat.one_le_pow _ _ (by decide : 0 < 2)).trans hm
  have h := primeProductReciprocalMass_upper 1 m hm1
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one] at h
  apply h.trans
  apply (div_le_one (by positivity : (0 : ℝ) < (m : ℝ) + 1)).mpr
  have hmR : (2 : ℝ)^64 ≤ (m : ℝ) := by exact_mod_cast hm
  linarith only [hmR]

/-- Even exact knowledge of the first R product-modulus main terms does
not, as an abstract moment statement, force any mass above R factors. -/
theorem exists_truncated_product_moment_model (R m : ℕ) (hm : 2^64 ≤ m) :
    ∃ w : ℕ → ℝ,
      (∀ j, 0 ≤ w j) ∧ (∀ j, R < j → w j = 0) ∧
      (∑ j ∈ range (R + 1), w j) = 1 ∧
      ∀ k ≤ R, (∑ j ∈ range (R + 1), (j.choose k : ℝ) * w j) = primeProductReciprocalMass k m := by
  apply exists_truncated_binomial_moment_model R (fun k => primeProductReciprocalMass k m)
    (primeProductReciprocalMass_zero m) (fun k _ => primeProductReciprocalMass_nonneg k m)
  intro k hk
  exact (primeProductReciprocalMass_succ_ratio k m).trans
    (mul_le_of_le_one_left (primeProductReciprocalMass_nonneg k m) (primeProductReciprocalMass_one_le_one m hm))

/-- The requested next main term is strictly positive at large scales,
while a model matching all the lower ones still has next moment zero. -/
theorem eventually_product_moment_model_with_zero_next (R : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∃ w : ℕ → ℝ,
      (∀ j, 0 ≤ w j) ∧ (∀ j, R < j → w j = 0) ∧
      (∑ j ∈ range (R + 1), w j) = 1 ∧
      (∀ k ≤ R, (∑ j ∈ range (R + 1), (j.choose k : ℝ) * w j) = primeProductReciprocalMass k m) ∧
      0 < primeProductReciprocalMass (R + 1) m ∧
      (∑ j ∈ range (R + 1), (j.choose (R + 1) : ℝ) * w j) = 0 := by
  filter_upwards [eventually_ge_atTop (2^64),
    eventually_nat_poly_le_two_pow 1 (4096 * (R + 1)) 1] with m hm hsmall
  obtain ⟨w, hw, hsupp, hnorm, hmoment⟩ := exists_truncated_product_moment_model R m hm
  refine ⟨w, hw, hsupp, hnorm, hmoment, ?_, ?_⟩
  · have hsmall' : 4096 * (R + 1) * (m + 1) ≤ progressionScaleN m := by
      have hpow : 2^m ≤ progressionScaleN m := Nat.pow_le_pow_right (by decide) (by omega)
      simpa only [one_mul, pow_one] using hsmall.trans hpow
    have hlo := primeProductModuli_reciprocal_lower (R + 1) m hsmall'
    have hC : (0 : ℝ) < primeProductMassConstant (R + 1) := by
      exact_mod_cast primeProductMassConstant_pos (R + 1)
    have hmR : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hpos : (0 : ℝ) < 1 / ((primeProductMassConstant (R + 1) : ℝ) * ((m : ℝ) + 1)^(R + 1)) :=
      div_pos (by norm_num) (mul_pos hC (pow_pos hmR _))
    exact hpos.trans_le hlo
  · apply sum_eq_zero
    intro j hj
    rw [Nat.choose_eq_zero_of_lt (mem_range.mp hj), Nat.cast_zero, zero_mul]

end Erdos821
