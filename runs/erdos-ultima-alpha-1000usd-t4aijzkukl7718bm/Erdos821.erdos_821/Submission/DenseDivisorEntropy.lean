import Submission.DensePredecessorSupport

/-!
# Divisor-count loss for dense prime-predecessor products

A small prime support bounds the logarithm of the divisor count. The
estimate is on the scale X/log X for the full predecessor product, not
on the scale of arbitrary selected outputs. No amplification is asserted.
-/

open Nat Finset Filter
open scoped Classical BigOperators Topology

namespace Erdos821.DensePredecessors

set_option maxHeartbeats 2000000

lemma factorization_mass_le_log (n : ℕ) :
    (∑ q ∈ n.primeFactors, (n.factorization q : ℝ)) ≤ Real.log n/Real.log 2 := by
  apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  rw [sum_mul, Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
  apply sum_le_sum
  intro q hq
  exact mul_le_mul_of_nonneg_left
    (Real.log_le_log (by norm_num) (by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).two_le))
    (Nat.cast_nonneg _)

lemma log_one_add_le_log_scale (v A : ℝ) (hv : 0 ≤ v) (hA : 1 ≤ A) :
    Real.log (v+1) ≤ Real.log A+v/A := by
  have hA0 : 0 < A := by linarith
  have hv0 : 0 < v+1 := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos hv0 hA0)
  rw [Real.log_div hv0.ne' hA0.ne'] at h
  have h1 : (1 : ℝ)/A ≤ 1 := (div_le_one hA0).mpr hA
  rw [add_div] at h
  linarith

/-- A finite entropy bound retaining the number of distinct prime labels. -/
theorem log_card_divisors_le_support (n : ℕ) (hn : n ≠ 0) (A : ℝ) (hA : 1 ≤ A) :
    Real.log (n.divisors.card : ℝ) ≤
      n.primeFactors.card*Real.log A + Real.log n/(A*Real.log 2) := by
  have hA0 : 0 < A := by linarith
  rw [Nat.card_divisors hn, Nat.cast_prod, Real.log_prod (fun q _ => by positivity)]
  calc
    _ ≤ ∑ q ∈ n.primeFactors, (Real.log A+(n.factorization q : ℝ)/A) := by
      apply sum_le_sum
      intro q hq
      push_cast
      exact log_one_add_le_log_scale _ A (Nat.cast_nonneg _) hA
    _ = n.primeFactors.card*Real.log A +
        (∑ q ∈ n.primeFactors, (n.factorization q : ℝ))/A := by
      rw [sum_add_distrib, ← sum_div]
      simp
    _ ≤ _ := by
      apply _root_.add_le_add le_rfl
      have h := div_le_div_of_nonneg_right (factorization_mass_le_log n) hA0.le
      simpa only [div_div, mul_comm A (Real.log 2)] using h

lemma log_predecessorProduct_upper (X : ℕ) :
    Real.log (predecessorProduct X : ℝ) ≤ Real.log 4*X := by
  apply le_trans _ (Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg X))
  rw [Sieve.theta_nat_eq_sum_primesBelow]
  unfold predecessorProduct
  rw [Nat.cast_prod, Real.log_prod (fun p hp => by
    exact_mod_cast (Nat.sub_pos_of_lt (Nat.mem_primesBelow.mp hp).2.one_lt).ne')]
  apply sum_le_sum
  intro p hp
  exact Real.log_le_log
    (by exact_mod_cast Nat.sub_pos_of_lt (Nat.mem_primesBelow.mp hp).2.one_lt)
    (by exact_mod_cast Nat.sub_le p 1)

lemma log_divisors_predecessorProduct_le (m : ℕ) (hm : 1 ≤ m) :
    Real.log ((predecessorProduct (2^(128*m^2))).divisors.card : ℝ) ≤
      (support (2^(128*m^2))).card*(6*Real.sqrt (m : ℝ)) +
        2*(2 : ℝ)^(128*m^2)/(m : ℝ)^3 := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hA : (1 : ℝ) ≤ (m : ℝ)^3 := one_le_pow₀ hmR
  have h := log_card_divisors_le_support (predecessorProduct (2^(128*m^2)))
    (predecessorProduct_pos _).ne' ((m : ℝ)^3) hA
  rw [predecessorProduct_primeFactors] at h
  apply h.trans (_root_.add_le_add ?_ ?_)
  · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    rw [Real.log_pow]
    have hlog := Real.log_le_rpow_div hm0.le (by norm_num : (0 : ℝ) < 1/2)
    rw [← Real.sqrt_eq_rpow] at hlog
    norm_num at hlog ⊢
    linarith
  · have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog4 : Real.log 4 = 2*Real.log 2 := by
      rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
      norm_num
    have hb := div_le_div_of_nonneg_right
      (log_predecessorProduct_upper (2^(128*m^2)))
      (show 0 ≤ (m : ℝ)^3*Real.log 2 by positivity)
    apply hb.trans_eq
    rw [hlog4]
    push_cast
    field_simp

/-- Explicit divisor-count error on the scale X/log X. -/
theorem scaled_log_divisors_bound (m : ℕ) (hm : 1 ≤ m) :
    (m : ℝ)^2 * Real.log ((predecessorProduct (2^(128*m^2))).divisors.card : ℝ) /
      (2 : ℝ)^(128*m^2) ≤
        12*cofactorSieveConstant/Real.sqrt (m : ℝ) +
          24*(m : ℝ)^3*(1/2 : ℝ)^m+2/(m : ℝ) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hs0 : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hm0
  have hs2 := Real.sq_sqrt hm0.le
  have hsle : Real.sqrt (m : ℝ) ≤ m := by nlinarith
  have hi0 : 0 ≤ (m : ℝ)⁻¹ := inv_nonneg.mpr hm0.le
  have hi1 : (m : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hm0).mpr hmR
  have hi2 : (m : ℝ)⁻¹^2 ≤ (m : ℝ)⁻¹ := by nlinarith
  have hid : Real.sqrt (m : ℝ)*(m : ℝ)⁻¹ = (Real.sqrt (m : ℝ))⁻¹ := by
    apply (mul_right_cancel₀ hs0.ne')
    field_simp [hm0.ne']
    nlinarith only [hs2]
  have hbase := mul_le_mul_of_nonneg_left (log_divisors_predecessorProduct_le m hm)
    (div_nonneg (sq_nonneg (m : ℝ)) (by positivity : (0 : ℝ) ≤ (2 : ℝ)^(128*m^2)))
  have hbase' :
      (m : ℝ)^2 * Real.log ((predecessorProduct (2^(128*m^2))).divisors.card : ℝ) /
        (2 : ℝ)^(128*m^2) ≤
      6*Real.sqrt (m : ℝ)*((m : ℝ)^2*(support (2^(128*m^2))).card/
        (2 : ℝ)^(128*m^2))+2/(m : ℝ) := by
    convert hbase using 1 <;> field_simp [hm0.ne']
  have hbound := mul_le_mul_of_nonneg_left (scaled_support_bound m hm)
    (show 0 ≤ 6*Real.sqrt (m : ℝ) by positivity)
  have hfirst : 6*Real.sqrt (m : ℝ)*
      (cofactorSieveConstant*((m : ℝ)⁻¹^2+(m : ℝ)⁻¹)) ≤
        12*cofactorSieveConstant/Real.sqrt (m : ℝ) := by
    have hc := mul_le_mul_of_nonneg_left
      (show (m : ℝ)⁻¹^2+(m : ℝ)⁻¹ ≤ 2*(m : ℝ)⁻¹ by linarith)
      (show 0 ≤ 6*Real.sqrt (m : ℝ)*cofactorSieveConstant by
        positivity [cofactorSieveConstant_nonneg])
    calc
      _ ≤ 12*cofactorSieveConstant*(Real.sqrt (m : ℝ)*(m : ℝ)⁻¹) := by nlinarith only [hc]
      _ = _ := by rw [hid,div_eq_mul_inv]
  have hsecond := mul_le_mul_of_nonneg_right hsle
    (show 0 ≤ 24*(m : ℝ)^2*(1/2 : ℝ)^m by positivity)
  nlinarith only [hbase',hbound,hfirst,hsecond]

/-- The logarithm of the divisor-count loss is o(X/log X) at the full
prime-pool scales. This is stronger than a generic subpower bound in N. -/
theorem tendsto_scaled_log_divisors :
    Tendsto (fun m : ℕ => (m : ℝ)^2 *
      Real.log ((predecessorProduct (2^(128*m^2))).divisors.card : ℝ) /
        (2 : ℝ)^(128*m^2)) atTop (𝓝 0) := by
  have hi : Tendsto (fun m : ℕ => (m : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hs : Tendsto (fun m : ℕ => (Real.sqrt (m : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hg := tendsto_pow_const_mul_const_pow_of_lt_one 3
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)
  have ht : Tendsto (fun m : ℕ =>
      12*cofactorSieveConstant/Real.sqrt (m : ℝ) +
        24*(m : ℝ)^3*(1/2 : ℝ)^m+2/(m : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,zero_add,mul_assoc] using
      ((hs.const_mul (12*cofactorSieveConstant)).add (hg.const_mul 24)).add (hi.const_mul 2)
  have hnonneg (m : ℕ) : 0 ≤ (m : ℝ)^2 *
      Real.log ((predecessorProduct (2^(128*m^2))).divisors.card : ℝ) /
        (2 : ℝ)^(128*m^2) := by
    have hcard : 1 ≤ (predecessorProduct (2^(128*m^2))).divisors.card := by
      apply card_pos.mpr
      exact ⟨1,Nat.mem_divisors.mpr ⟨one_dvd _,(predecessorProduct_pos _).ne'⟩⟩
    exact div_nonneg (mul_nonneg (sq_nonneg _) (Real.log_nonneg (by exact_mod_cast hcard)))
      (by positivity)
  apply squeeze_zero' (Eventually.of_forall hnonneg) _ ht
  filter_upwards [eventually_ge_atTop 1] with m hm
  exact scaled_log_divisors_bound m hm

/-- The number of divisor outputs is subexponential on the prime-count
scale. This can quantify one loss in a subsequent squarefree reduction. -/
theorem eventually_divisors_le_exp_prime_scale (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ((predecessorProduct (2^(128*m^2))).divisors.card : ℝ) ≤
      Real.exp (ε*(2 : ℝ)^(128*m^2)/(m : ℝ)^2) := by
  filter_upwards [tendsto_scaled_log_divisors.eventually_lt_const hε,
    eventually_ge_atTop 1] with m hm hm1
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hcard : 0 < (predecessorProduct (2^(128*m^2))).divisors.card := by
    apply card_pos.mpr
    exact ⟨1,Nat.mem_divisors.mpr ⟨one_dvd _,(predecessorProduct_pos _).ne'⟩⟩
  have hcardR : (0 : ℝ) < (predecessorProduct (2^(128*m^2))).divisors.card := by
    exact_mod_cast hcard
  have h1 := (div_lt_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ)^(128*m^2))).mp hm
  have hlog : Real.log ((predecessorProduct (2^(128*m^2))).divisors.card : ℝ) ≤
      ε*(2 : ℝ)^(128*m^2)/(m : ℝ)^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hmR)).mpr
    nlinarith only [h1]
  rw [← Real.exp_log hcardR]
  exact Real.exp_le_exp.mpr hlog

end Erdos821.DensePredecessors
