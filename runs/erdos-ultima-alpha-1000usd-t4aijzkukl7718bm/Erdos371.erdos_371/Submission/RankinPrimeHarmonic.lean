import Submission.RankinSmoothBound

/-! A uniform Rankin bound retaining the prime harmonic sum. Unlike the older
full-harmonic majorant, it allows a nearly-power moving smoothness boundary. -/
namespace Erdos371
open Finset Filter
open scoped Topology
set_option autoImplicit false

lemma prime_neg_rpow_sum_le_primeHarmonic (B : ℕ) (s : ℝ) (hs : s ≤ 1) :
    (∑ p ∈ B.primesBelow, (p : ℝ)^(-s)) ≤ (B : ℝ)^(1-s)*primeHarmonic B := by
  have hp : (∑ p ∈ B.primesBelow, (1 : ℝ)/p) ≤ primeHarmonic B := by
    unfold primeHarmonic primeReciprocalSum
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hpB,hpp⟩ := Nat.mem_primesBelow.mp hp
      exact mem_filter.mpr ⟨mem_range.mpr (by omega),hpp⟩
    · intros; positivity
  calc
    _ ≤ ∑ p ∈ B.primesBelow, (B : ℝ)^(1-s)*(1/p) := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hpB,hpp⟩ := Nat.mem_primesBelow.mp hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      have he : (p : ℝ)^(-s) = (p : ℝ)^(1-s)/p := by
        have h := Real.rpow_sub hp0 (1-s) 1
        rw [Real.rpow_one,show 1-s-1 = -s by ring] at h
        exact h
      rw [he,mul_one_div]
      exact div_le_div_of_nonneg_right
        (Real.rpow_le_rpow hp0.le (by exact_mod_cast hpB.le) (by linarith)) hp0.le
    _ = (B : ℝ)^(1-s)*(∑ p ∈ B.primesBelow, (1 : ℝ)/p) := (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)

theorem smooth_rankin_primeHarmonic_bound (B N : ℕ) (s : ℝ)
    (hs : 1/2 ≤ s) (hs' : s ≤ 1) :
    (Nat.smoothNumbersUpTo N B).card ≤
      (N : ℝ)^s * Real.exp (4*(B : ℝ)^(1-s)*primeHarmonic B) := by
  apply (smooth_rankin_bound B N s (by linarith)).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∏ p ∈ B.primesBelow, Real.exp (4*(p : ℝ)^(-s)) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact inv_nonneg.mpr (by have := prime_neg_rpow_le_three_quarters p (Nat.mem_primesBelow.mp hp).2 s hs; linarith)
      · intro p hp
        exact geometric_inv_le_exp_four _ (by positivity)
          (prime_neg_rpow_le_three_quarters p (Nat.mem_primesBelow.mp hp).2 s hs)
    _ = Real.exp (4*∑ p ∈ B.primesBelow, (p : ℝ)^(-s)) := by rw [mul_sum,Real.exp_sum]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [prime_neg_rpow_sum_le_primeHarmonic B s hs'])

/-- The logarithm of the Euler-product loss is only linear in j here. -/
theorem smooth_double_power_rankin_ratio (j k : ℕ) (hj : 1 ≤ j) :
    (Nat.smoothNumbersUpTo (2^(k+1)) (2^(2^j))).card / (2 : ℝ)^(k+1) ≤
      Real.exp (96*(j+1 : ℝ)-((k+1 : ℝ)/(2 : ℝ)^j)*Real.log 2) := by
  let s : ℝ := 1-1/(2 : ℝ)^j
  have hpow : (2 : ℝ) ≤ 2^j := by
    simpa only [pow_one] using (pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤2) hj)
  have hs : 1/2 ≤ s := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<2) hpow
    dsimp [s]; linarith
  have hs' : s ≤ 1 := by dsimp [s]; exact sub_le_self _ (by positivity)
  have hB : ((2 : ℝ)^(2^j : ℕ))^(1-s) = 2 := by
    dsimp only [s]
    rw [show 1-(1-1/(2 : ℝ)^j) = 1/(2 : ℝ)^j by ring,
      ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ)≤2)]
    push_cast
    rw [mul_one_div_cancel (by positivity : (2 : ℝ)^j ≠ 0),Real.rpow_one]
  have h := smooth_rankin_primeHarmonic_bound (2^(2^j)) (2^(k+1)) s hs hs'
  push_cast at h
  rw [hB] at h
  have he := Real.exp_le_exp.mpr (show 4*2*primeHarmonic (2^(2^j)) ≤ 96*(j+1 : ℝ) by
    have h := primeHarmonic_double_power_le j; linarith)
  have hb := h.trans (mul_le_mul_of_nonneg_left he (by positivity))
  have hd := div_le_div_of_nonneg_right hb (by positivity : (0 : ℝ)≤2^(k+1))
  apply hd.trans_eq
  have hden : (2 : ℝ)^(k+1) = Real.exp ((k+1 : ℝ)*Real.log 2) := by
    have h := (Real.exp_log (pow_pos (by norm_num : (0 : ℝ)<2) (k+1))).symm
    simpa only [Real.log_pow,Nat.cast_add,Nat.cast_one] using h
  rw [Real.rpow_def_of_pos (by positivity),Real.log_pow]
  conv_lhs => arg 2; rw [hden]
  rw [← Real.exp_add,← Real.exp_sub]
  congr 1
  dsimp [s]
  push_cast
  ring

#print axioms smooth_rankin_primeHarmonic_bound
#print axioms smooth_double_power_rankin_ratio
end Erdos371
