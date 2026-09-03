import Submission.LogarithmicSignedReduction

/-! The first nonlinear odd logarithmic moment reduces to a specific mixed
correlation. Neither its cancellation nor the density conjecture is proved. -/

namespace Erdos371
open Finset Filter

noncomputable def cubicLogSkew (N n : ℕ) : ℝ :=
  (normalizedPrimeLog N n)^2*normalizedPrimeLog N (n+1) -
    normalizedPrimeLog N n*(normalizedPrimeLog N (n+1))^2

lemma logDifference_cube (N n : ℕ) :
    (logDifference N n)^3 =
      (normalizedPrimeLog N (n+1))^3-(normalizedPrimeLog N n)^3+3*cubicLogSkew N n := by
  rw [logDifference_eq_sub]
  unfold cubicLogSkew
  ring

lemma logDifference_cube_sum (N : ℕ) :
    (∑ n ∈ range N, (logDifference N n)^3) =
      (normalizedPrimeLog N N)^3+3*(∑ n ∈ range N, cubicLogSkew N n) := by
  simp_rw [logDifference_cube]
  rw [sum_add_distrib,sum_range_sub (fun n => (normalizedPrimeLog N n)^3) N,← mul_sum]
  simp [normalizedPrimeLog]

lemma normalizedPrimeLog_boundary_cube_tendsto_zero :
    Tendsto (fun N : ℕ => (normalizedPrimeLog N N)^3/N) atTop (nhds 0) := by
  apply squeeze_zero' _ _ (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  · filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
    exact div_nonneg (pow_nonneg (normalizedPrimeLog_mem_unit N N hN le_rfl).1 _) (Nat.cast_nonneg N)
  · filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
    have h := pow_le_pow_left₀ (normalizedPrimeLog_mem_unit N N hN le_rfl).1
      (normalizedPrimeLog_mem_unit N N hN le_rfl).2 3
    norm_num only [one_pow] at h
    exact div_le_div_of_nonneg_right h (Nat.cast_nonneg N)

/-- Cancellation of the cubic difference is precisely cancellation of this
mixed skew correlation, up to a vanishing endpoint term. This is not claimed
to be equivalent to the original density conjecture. -/
theorem logDifference_cube_cancellation_iff :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, (logDifference N n)^3)/N) atTop (nhds 0) ↔
      Tendsto (fun N : ℕ => (∑ n ∈ range N, cubicLogSkew N n)/N) atTop (nhds 0) := by
  have he (N : ℕ) : (∑ n ∈ range N, (logDifference N n)^3)/N =
      (normalizedPrimeLog N N)^3/N+3*((∑ n ∈ range N, cubicLogSkew N n)/N) := by
    rw [logDifference_cube_sum,add_div,mul_div_assoc]
  constructor
  · intro h
    have ht := (h.sub normalizedPrimeLog_boundary_cube_tendsto_zero).div_const 3
    simp only [sub_zero,zero_div] at ht
    apply ht.congr'
    apply Eventually.of_forall
    intro N
    dsimp only
    rw [he]
    ring
  · intro h
    have ht := normalizedPrimeLog_boundary_cube_tendsto_zero.add (h.const_mul 3)
    simp only [mul_zero,add_zero] at ht
    exact ht.congr' (Eventually.of_forall fun N => (he N).symm)

/-- Even the cubic component of the sufficient continuous-test criterion
requires the mixed skew correlation above. The first-moment identity alone
cannot supply this implication's hypothesis. -/
lemma continuous_odd_cancellation_implies_cubic_skew
    (hcancel : ∀ f : ℝ → ℝ, Continuous f → (∀ x, f (-x) = -f x) →
      Tendsto (fun N : ℕ => (∑ n ∈ range N, f (logDifference N n))/N) atTop (nhds 0)) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, cubicLogSkew N n)/N) atTop (nhds 0) := by
  apply logDifference_cube_cancellation_iff.mp
  exact hcancel (fun x => x^3) (continuous_id.pow 3) (by intro x; ring)

#print axioms logDifference_cube_cancellation_iff
#print axioms continuous_odd_cancellation_implies_cubic_skew
end Erdos371
