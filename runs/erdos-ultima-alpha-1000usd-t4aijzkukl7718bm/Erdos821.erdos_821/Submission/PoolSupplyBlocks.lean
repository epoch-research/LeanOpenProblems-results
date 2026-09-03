import Submission.PoolSupplyScales

/-!
# Applying retained-pool bounds to the actual wide two-prime pool

All narrow-block size and support hypotheses are discharged uniformly
for the bounded enlargement of the prime cutoff.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 5000000

def poolMultiplierK (m : ℕ) : ℕ := 64*20000000*m-1
def poolMultiplierL (m : ℕ) : ℕ := 256*m+2

lemma poolMultiplier_end (m : ℕ) (hm : 1 ≤ m) :
    poolMultiplierK m+poolMultiplierL m = 64*20000004*m+1 := by
  unfold poolMultiplierK poolMultiplierL
  omega

lemma poolMultiplier_support (m : ℕ) (hm : 1 ≤ m) :
    ∀ c ∈ widePairPool 10000000 m,
      2^(poolMultiplierK m)<c ∧ c ≤ 2^(poolMultiplierK m+poolMultiplierL m) := by
  intro c hc
  have hb := widePairPool_bounds 10000000 m c hc
  constructor
  · apply lt_of_lt_of_le _ hb.2.1
    apply Nat.pow_lt_pow_right (by decide)
    unfold poolMultiplierK
    omega
  · apply hb.2.2.trans
    rw [poolMultiplier_end m hm]
    apply Nat.pow_le_pow_right (by decide)
    omega

lemma poolMultiplier_block_scales (m X : ℕ) (hm : 1000000 ≤ m)
    (hXlo : independentN 40000020 m ≤ X) (hXhi : X ≤ independentN 40000021 m) :
    ∀ i ∈ range (poolMultiplierL m), ∀ j ∈ range (2^10),
      let D := multiplierUpper (poolMultiplierK m+i) 10 j
      let H := X/multiplierLower (poolMultiplierK m+i) 10 j
      cofactorScale 3 (2*cofactorDyadicIndex 100000000 (64*20000014*m)) ≤ H/2^(64*20000014*m) ∧
      cofactorScale 99990001 (2*cofactorDyadicIndex 100000000 (64*20000014*m)) ≤ D*(H/2^(64*20000014*m)) ∧
      D*(H/2^(64*16080000*m)) ≤ cofactorScale 150000000 (2*cofactorDyadicIndex 100000000 (64*16080000*m+1)) := by
  intro i hi j hj
  have hkr : 10 ≤ poolMultiplierK m+i := by unfold poolMultiplierK; omega
  have hj0 : j < 2^10 := mem_range.mp hj
  have hi0 := mem_range.mp hi
  have hCup : multiplierLower (poolMultiplierK m+i) 10 j ≤ 2^(64*20000004*m+1) := by
    apply (multiplierLower_le_upper _ _ _).trans
    apply (multiplierUpper_upper _ _ _ hj0 hkr).trans
    rw [← poolMultiplier_end m (by omega)]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  exact ⟨pool_supply_short_prefix m X _ hm hXlo (multiplierLower_pos _ _ _) hCup,
    pool_supply_product_lower m X _ _ hm hXlo (multiplierLower_pos _ _ _)
      (multiplierLower_le_upper _ _ _) hCup,
    pool_supply_product_upper m X _ _ hXhi (multiplierUpper_le_two_lower _ _ _)⟩

lemma poolMultiplier_rough (m : ℕ) (hm : 1000000 ≤ m) :
    ∀ c ∈ widePairPool 10000000 m, ∀ p : ℕ, p.Prime →
      p ≤ cofactorScale 99990000 (cofactorDyadicIndex 100000000 (64*20000014*m)) → ¬p ∣ c := by
  intro c hc p hp hpz hpc
  obtain ⟨⟨u,v⟩,huv,rfl⟩ := mem_image.mp hc
  obtain ⟨hu,hv⟩ := mem_product.mp huv
  have hz := pool_supply_sieve_below_multiplier_primes m hm
  rcases hp.dvd_mul.mp hpc with hpu | hpv
  · have he := (Nat.prime_dvd_prime_iff_eq hp (widePairLeft_prime 10000000 m u hu)).mp hpu
    have hb := (widePairPools_bounds 10000000 m u (Or.inl hu)).2.1
    omega
  · have he := (Nat.prime_dvd_prime_iff_eq hp (widePairRight_prime 10000000 m v hv)).mp hpv
    have hb := (widePairPools_bounds 10000000 m v (Or.inr hv)).2.1
    omega

noncomputable def poolLongCoefficient : ℝ :=
  (2*(100000000 : ℝ)/99990000)*(1+1/(2 : ℝ)^10)^2

lemma poolLongCoefficient_pos : 0 < poolLongCoefficient := by
  unfold poolLongCoefficient
  norm_num

lemma sum_inverse_le_poolTotientMass (P : Finset ℕ) (hP : ∀ c ∈ P, 0 < c) :
    (∑ c ∈ P, (c : ℝ)⁻¹) ≤ poolTotientMass P := by
  apply sum_le_sum
  intro c hc
  have hφ : (0 : ℝ)<c.totient := by exact_mod_cast Nat.totient_pos.mpr (hP c hc)
  have hc0 : (0 : ℝ)<c := by exact_mod_cast hP c hc
  exact (inv_le_inv₀ hc0 hφ).mpr (Nat.cast_le.mpr (Nat.totient_le c))

/-- The averaged long-range bound applies to the real prime-product pool,
not a hypothetical positive-density support. -/
theorem exists_pool_long_raw_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ m : ℕ in atTop, ∀ X : ℕ,
      independentN 40000020 m ≤ X → X ≤ independentN 40000021 m →
      (∑ c ∈ widePairPool 10000000 m,
        ((hyperbolicPrimePairPool c (X/c) (2^(128*8040000*m)) (2^(128*10000007*m))).card : ℝ)) ≤
        (poolLongCoefficient*(X : ℝ)*poolTotientMass (widePairPool 10000000 m)/(Real.log 2)^2)*
          (Real.log 2*(1/(128*(8040000 : ℝ)*m-1)-1/(128*(10000007 : ℝ)*m-1))+
            2*C/(128*(8040000 : ℝ)*m)^2)+
        ((1+1/(2 : ℝ)^10)*(X : ℝ)*(256*(m : ℝ)+2)*(2 : ℝ)^10/
          ((Real.log 2)^2*(128*(8040000 : ℝ)*m+1)^3))*
            (1/(128*(8040000 : ℝ)*m-1)-1/(128*(10000007 : ℝ)*m-1)) := by
  obtain ⟨C,hC,K₀,HK⟩ := exists_wide_pool_hyperbolic_bound 1 99990000 3 99990001 150000000 100000000 10 10 3
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 1 (by norm_num)
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ge_atTop (max 1000000 K₀)] with m hm
  have hm0 : 1000000 ≤ m := (le_max_left _ _).trans hm
  have hm1 : 1 ≤ m := by omega
  have hmK : K₀ ≤ m := (le_max_right _ _).trans hm
  intro X hXlo hXhi
  have hsum : 64*16080000*m+64*3920014*m=64*20000014*m := by ring
  have h := HK (64*16080000*m) (64*3920014*m) X (poolMultiplierK m) (poolMultiplierL m)
    (by omega) (by omega) (by unfold poolMultiplierK; omega) (widePairPool 10000000 m)
    (poolMultiplier_support m hm1) (by rw [hsum]; exact poolMultiplier_rough m hm0)
    (by rw [hsum]; exact poolMultiplier_block_scales m X hm0 hXlo hXhi)
  have hraw : (∑ c ∈ widePairPool 10000000 m,
      ((hyperbolicPrimePairPool c (X/c) (2^(128*8040000*m)) (2^(128*10000007*m))).card : ℝ)) ≤
      (poolLongCoefficient*(X : ℝ)*(∑ c ∈ widePairPool 10000000 m, (c : ℝ)⁻¹)/(Real.log 2)^2)*
        (Real.log 2*(1/(128*(8040000 : ℝ)*m-1)-1/(128*(10000007 : ℝ)*m-1))+
          2*C/(128*(8040000 : ℝ)*m)^2)+
      ((1+1/(2 : ℝ)^10)*(X : ℝ)*(256*(m : ℝ)+2)*(2 : ℝ)^10/
        ((Real.log 2)^2*(128*(8040000 : ℝ)*m+1)^3))*
          (1/(128*(8040000 : ℝ)*m-1)-1/(128*(10000007 : ℝ)*m-1)) := by
    rw [hsum] at h
    convert h using 1
    unfold poolLongCoefficient poolMultiplierL
    push_cast
    ring
  apply hraw.trans
  have hΔ : 0 ≤ 1/(128*(8040000 : ℝ)*m-1)-1/(128*(10000007 : ℝ)*m-1) := by
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    apply sub_nonneg.mpr (one_div_le_one_div_of_le (by nlinarith) (by nlinarith))
  have hcoef : 0 ≤ (poolLongCoefficient*(X : ℝ)/(Real.log 2)^2)*
      (Real.log 2*(1/(128*(8040000 : ℝ)*m-1)-1/(128*(10000007 : ℝ)*m-1))+2*C/(128*(8040000 : ℝ)*m)^2) := by
    have := poolLongCoefficient_pos.le
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    positivity
  have hrec := mul_le_mul_of_nonneg_left
    (sum_inverse_le_poolTotientMass (widePairPool 10000000 m)
      (fun c hc => (by have := (widePairPool_bounds 10000000 m c hc).1; omega))) hcoef
  apply _root_.add_le_add _ le_rfl
  convert hrec using 1 <;> ring

end Erdos821.AnalyticSieve
