import Submission.SmoothSkewPrimeAveraging
import Submission.WeightedPrimeHarmonic

/-! Uniform logarithmic prime averaging. The full logarithm of an integer
can be replaced in mean by the logarithm of its radical. Applied to smooth
skew this gives a centered prime-log-weighted identity, but does not prove
cancellation of its shifted smooth-number values. -/

namespace Erdos371

open Finset Filter
open FiniteSieve
open scoped Topology

lemma squarefreeSmallPrimeLog_le_log (B n : ℕ) (hn : 0 < n) :
    squarefreeSmallPrimeLog B n ≤ Real.log n := by
  apply le_trans _ (smallPrimeLog_le_log B n hn.ne')
  unfold squarefreeSmallPrimeLog smallPrimeLog
  apply sum_le_sum
  intro p hp
  have hpp := (Nat.mem_primesBelow.mp hp).2
  by_cases hd : p ∣ n
  · rw [if_pos hd]
    have hv : (1 : ℝ) ≤ n.factorization p := by
      exact_mod_cast hpp.factorization_pos_of_dvd hn.ne' hd
    have h := mul_le_mul_of_nonneg_right hv (Real.log_natCast_nonneg p)
    simpa only [one_mul] using h
  · rw [if_neg hd]
    positivity

lemma squarefreeSmallPrimeLog_sum (B N : ℕ) :
    (∑ n ∈ range N, squarefreeSmallPrimeLog B (n+1)) =
      ∑ p ∈ B.primesBelow, ((N/p : ℕ) : ℝ) * Real.log p := by
  unfold squarefreeSmallPrimeLog
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  rw [← sum_filter, sum_const, nsmul_eq_mul, Nat.card_multiples]

lemma primeLogSum_upper (N : ℕ) :
    (∑ p ∈ (N+1).primesBelow, Real.log p) ≤ Real.log 4 * N := by
  have he : (N+1).primesBelow = (Ioc 0 N).filter Nat.Prime := by
    ext p
    simp only [Nat.mem_primesBelow, mem_filter, mem_Ioc]
    constructor
    · rintro ⟨hpN,hp⟩
      exact ⟨⟨hp.pos, by omega⟩, hp⟩
    · rintro ⟨⟨_, hpN⟩, hp⟩
      exact ⟨by omega, hp⟩
  simpa only [Chebyshev.theta, Nat.floor_natCast, ← he] using
    Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg (α := ℝ) N)

noncomputable def logPrimeAverageConstant : ℝ :=
  1 + primePowerErrorConstant + Real.log 4

lemma squarefreeSmallPrimeLog_sum_lower (N : ℕ) (hN : 0 < N) :
    N * Real.log N - N * logPrimeAverageConstant ≤
      ∑ n ∈ range N, squarefreeSmallPrimeLog (N+1) (n+1) := by
  have ht (p : ℕ) (hp : p ∈ (N+1).primesBelow) :
      (N : ℝ)*(Real.log p/p) - Real.log p ≤
        ((N/p : ℕ) : ℝ)*Real.log p := by
    have h := nat_div_rounding_error_norm_le_one N p (Nat.mem_primesBelow.mp hp).2.pos
    rw [Real.norm_eq_abs] at h
    have hh := (le_abs_self ((N : ℝ)/p - ((N/p : ℕ) : ℝ))).trans h
    have hm := mul_le_mul_of_nonneg_right hh (Real.log_natCast_nonneg p)
    have he : (N : ℝ)*(Real.log p/p) = ((N : ℝ)/p)*Real.log p := by ring
    rw [he]
    nlinarith
  have hs := sum_le_sum ht
  rw [sum_sub_distrib, ← mul_sum, ← squarefreeSmallPrimeLog_sum] at hs
  change (N : ℝ)*primeLogHarmonic N - _ ≤ _ at hs
  have hl := mul_le_mul_of_nonneg_left (primeLogHarmonic_lower N hN)
    (Nat.cast_nonneg (α := ℝ) N)
  have hu := primeLogSum_upper N
  unfold logPrimeAverageConstant
  nlinarith

/-- A one-dimensional, uniform L1 estimate for logarithmic prime averaging. -/
lemma squarefree_log_deficit_sum_bound (N : ℕ) (hN : 0 < N) :
    (∑ n ∈ range N, (Real.log N - squarefreeSmallPrimeLog (N+1) (n+1))) ≤
      N * logPrimeAverageConstant := by
  rw [sum_sub_distrib]
  simp only [sum_const, card_range, nsmul_eq_mul]
  linarith [squarefreeSmallPrimeLog_sum_lower N hN]

lemma squarefree_log_deficit_nonneg (N n : ℕ) (hn : n ∈ range N) :
    0 ≤ Real.log N - squarefreeSmallPrimeLog (N+1) (n+1) := by
  apply sub_nonneg.mpr
  apply (squarefreeSmallPrimeLog_le_log (N+1) (n+1) (by omega)).trans
  apply Real.log_le_log (by positivity)
  exact_mod_cast (show n+1 ≤ N by have := mem_range.mp hn; omega)

noncomputable def logPrimeAverage (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ (N+1).primesBelow, Real.log p * ∑ m ∈ Icc 1 (N/p), a (p*m)

lemma logPrimeAverage_eq_weighted (a : ℕ → ℝ) (N : ℕ) :
    logPrimeAverage a N =
      ∑ n ∈ range N, squarefreeSmallPrimeLog (N+1) (n+1) * a (n+1) := by
  unfold logPrimeAverage squarefreeSmallPrimeLog
  simp_rw [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  rw [← sum_positive_multiples a p N (Nat.mem_primesBelow.mp hp).2.pos, mul_sum]
  apply sum_congr rfl
  intro n hn
  split_ifs <;> simp

/-- The replacement error is uniform over all real observables bounded by one,
including observables depending arbitrarily on the averaging endpoint. -/
theorem logPrimeAverage_error_bound (a : ℕ → ℝ) (N : ℕ)
    (ha : ∀ n, |a n| ≤ 1) (hN : 0 < N) :
    |Real.log N * (∑ n ∈ range N, a (n+1)) - logPrimeAverage a N| ≤
      N * logPrimeAverageConstant := by
  rw [logPrimeAverage_eq_weighted, mul_sum, ← sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ range N, |Real.log N*a (n+1) -
        squarefreeSmallPrimeLog (N+1) (n+1)*a (n+1)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ range N, (Real.log N - squarefreeSmallPrimeLog (N+1) (n+1)) := by
      apply sum_le_sum
      intro n hn
      rw [← sub_mul, abs_mul, abs_of_nonneg (squarefree_log_deficit_nonneg N n hn)]
      exact mul_le_of_le_one_right (squarefree_log_deficit_nonneg N n hn) (ha (n+1))
    _ ≤ _ := squarefree_log_deficit_sum_bound N hN

noncomputable def centeredSmoothSkewPoint (B C n : ℕ) : ℝ :=
  smoothIndicator B n * (smoothIndicator C (n+1) - smoothIndicator C (n-1))

lemma centeredSmoothSkewPoint_abs_le_one (B C n : ℕ) :
    |centeredSmoothSkewPoint B C n| ≤ 1 := by
  unfold centeredSmoothSkewPoint smoothIndicator
  split_ifs <;> norm_num

lemma smoothCutoffSkew_centered_boundary (B C N : ℕ) :
    smoothCutoffSkew B C N - (∑ n ∈ range N, centeredSmoothSkewPoint B C (n+1)) =
      smoothIndicator B 1 * smoothIndicator C 0 -
        smoothIndicator B (N+1) * smoothIndicator C N := by
  unfold smoothCutoffSkew centeredSmoothSkewPoint
  rw [← sum_sub_distrib]
  have he (n : ℕ) :
      (smoothIndicator B (n+1)*smoothIndicator C (n+2) -
        smoothIndicator C (n+1)*smoothIndicator B (n+2)) -
      smoothIndicator B (n+1)*(smoothIndicator C ((n+1)+1)-smoothIndicator C ((n+1)-1)) =
      smoothIndicator B (n+1)*smoothIndicator C n -
        smoothIndicator B (n+2)*smoothIndicator C (n+1) := by
    simp only [Nat.add_sub_cancel, Nat.add_assoc, Nat.reduceAdd]
    ring
  simp_rw [he]
  exact sum_range_sub' (fun n => smoothIndicator B (n+1)*smoothIndicator C n) N

lemma smoothCutoffSkew_centered_error_le_one (B C N : ℕ) :
    |smoothCutoffSkew B C N - (∑ n ∈ range N, centeredSmoothSkewPoint B C (n+1))| ≤ 1 := by
  rw [smoothCutoffSkew_centered_boundary]
  unfold smoothIndicator
  split_ifs <;> norm_num

noncomputable def centeredLogPrimeSkew (B C N : ℕ) : ℝ :=
  ∑ p ∈ ((N+1).primesBelow.filter (· ≤ B)), Real.log p *
    ∑ m ∈ Icc 1 (N/p), smoothIndicator B m *
      (smoothIndicator C (p*m+1) - smoothIndicator C (p*m-1))

lemma centeredLogPrimeSkew_eq_average (B C N : ℕ) :
    centeredLogPrimeSkew B C N = logPrimeAverage (centeredSmoothSkewPoint B C) N := by
  unfold centeredLogPrimeSkew logPrimeAverage
  rw [sum_filter]
  apply sum_congr rfl
  intro p hp
  have hpp := (Nat.mem_primesBelow.mp hp).2
  by_cases hpB : p ≤ B
  · rw [if_pos hpB, mul_sum, mul_sum]
    apply sum_congr rfl
    intro m hm
    have hm0 : 0 < m := by have := (mem_Icc.mp hm).1; omega
    rw [centeredSmoothSkewPoint, smoothIndicator_mul_small B p m hpp.pos hm0 hpB]
  · rw [if_neg hpB]
    symm
    apply mul_eq_zero_of_right
    apply sum_eq_zero
    intro m hm
    have hm0 : 0 < m := by have := (mem_Icc.mp hm).1; omega
    have hpm : p ≤ Nat.maxPrimeFac (p*m) :=
      Nat.le_maxPrimeFac (mul_ne_zero hpp.ne_zero hm0.ne') hpp (Nat.dvd_mul_right p m)
    have hbad : ¬ Nat.maxPrimeFac (p*m) ≤ B := by omega
    simp only [centeredSmoothSkewPoint, smoothIndicator, if_neg hbad, zero_mul]

/-- The centered logarithmic prime average retains `N/p` and both shifted
arguments. Only the replacement error is controlled here. -/
theorem smoothCutoffSkew_log_prime_error (B C N : ℕ) (hN : 1 < N) :
    |smoothCutoffSkew B C N / N - centeredLogPrimeSkew B C N / (N * Real.log N)| ≤
      1 / (N : ℝ) + logPrimeAverageConstant / Real.log N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  let A := ∑ n ∈ range N, centeredSmoothSkewPoint B C (n+1)
  have hraw := logPrimeAverage_error_bound (centeredSmoothSkewPoint B C) N
    (centeredSmoothSkewPoint_abs_le_one B C) (by omega)
  rw [← centeredLogPrimeSkew_eq_average] at hraw
  have hcenter : |A / N - centeredLogPrimeSkew B C N / (N*Real.log N)| ≤
      logPrimeAverageConstant / Real.log N := by
    have hid : A / N - centeredLogPrimeSkew B C N / (N*Real.log N) =
        (Real.log N*A-centeredLogPrimeSkew B C N)/(N*Real.log N) := by
      field_simp
    rw [hid, abs_div, abs_of_pos (mul_pos hN' hl)]
    apply (div_le_iff₀ (mul_pos hN' hl)).mpr
    have hid' : logPrimeAverageConstant / Real.log N * ((N : ℝ)*Real.log N) =
        N * logPrimeAverageConstant := by field_simp
    rw [hid']
    exact hraw
  have hboundary : |smoothCutoffSkew B C N/N-A/N| ≤ 1/(N : ℝ) := by
    rw [← sub_div, abs_div, abs_of_pos hN']
    exact div_le_div_of_nonneg_right (smoothCutoffSkew_centered_error_le_one B C N) hN'.le
  exact (abs_sub_le (smoothCutoffSkew B C N/N) (A/N)
    (centeredLogPrimeSkew B C N/(N*Real.log N))).trans (add_le_add hboundary hcenter)

/-- Uniformity in the two cutoffs is complete: neither cutoff is required to
grow. The remaining centered prime average is not asserted to tend to zero. -/
theorem smoothCutoffSkew_log_prime_error_tendsto (B C : ℕ → ℕ) :
    Tendsto (fun N => smoothCutoffSkew (B N) (C N) N / N -
      centeredLogPrimeSkew (B N) (C N) N / (N * Real.log N)) atTop (nhds 0) := by
  have hl := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have he := tendsto_one_div_atTop_nhds_zero_nat.add
    (hl.inv_tendsto_atTop.const_mul logPrimeAverageConstant)
  simp only [mul_zero, add_zero] at he
  apply squeeze_zero_norm' _ he
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
  simpa only [Real.norm_eq_abs, div_eq_mul_inv, Pi.inv_apply] using
    smoothCutoffSkew_log_prime_error (B N) (C N) N hN

#print axioms logPrimeAverage_error_bound
#print axioms smoothCutoffSkew_log_prime_error
#print axioms smoothCutoffSkew_log_prime_error_tendsto

end Erdos371
