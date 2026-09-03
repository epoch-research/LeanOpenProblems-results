import Submission.ContinuousBuchstabIteration

/-! Quantitative finite-depth positivity of the continuous Buchstab model at
every level strictly greater than two. The endpoint itself remains zero
for the clamped lower profile. This is not a Jacobsthal bound. -/
namespace Erdos970.ContinuousBuchstab
open Real Set Filter MeasureTheory
open scoped Topology
set_option maxHeartbeats 1000000

lemma forcing_first_moment : (∫ s : ℝ in Ioi 1, s*forcing s) = 2 := by
  classical
  have he : (fun s : ℝ => s*forcing s) =ᶠ[ae (volume.restrict (Ioi 1))]
      (Iio 3).indicator (fun s => 3-s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : s ≠ 0 := by linarith [mem_Ioi.mp hs]
    by_cases h3 : s < 3
    · rw [indicator_of_mem (show s ∈ Iio (3 : ℝ) from h3)]
      dsimp only [forcing]
      rw [max_eq_left (by linarith : 0 ≤ 3-s)]
      field_simp
    · rw [indicator_of_notMem (show s ∉ Iio (3 : ℝ) from h3)]
      dsimp only [forcing]
      rw [max_eq_right (by linarith : 3-s ≤ 0), zero_div, mul_zero]
  rw [integral_congr_ae he, integral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio, Iio_inter_Ioi,
    ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 3),
    intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_const
      intervalIntegral.intervalIntegrable_id, intervalIntegral.integral_const, integral_id]
  norm_num

/-- The first-moment recurrence determines the total mass, without differentiating
any of the iterated profiles. -/
theorem mass_eq_moment_difference (n : ℕ) :
    mass n = 2+firstMoment n-firstMoment (n+1) := by
  have hg : IntegrableOn (fun s => s*forcing s) (Ioi 1) :=
    integrable_weighted_envelope forcing measurable_forcing 100 forcing_exp_envelope
  have hk : IntegrableOn (fun s => s*kernel (upperEnvelope n) s) (Ioi 1) :=
    integrable_weighted_envelope _ (measurable_kernel _ (measurable_upperEnvelope n))
      (2000*(19/20))
      (kernel_abs_le_exp _ (measurable_upperEnvelope n) 2000 (by norm_num) (upperEnvelope_exp_bound n))
  have hrec : firstMoment (n+1) = 2+(firstMoment n-mass n) := by
    unfold firstMoment
    simp_rw [upperEnvelope, mul_add]
    rw [integral_add hg hk, forcing_first_moment,
      kernel_first_moment _ (measurable_upperEnvelope n) 2000 (upperEnvelope_exp_bound n)]
    have he : (fun v : ℝ => (v-1)*upperEnvelope n v) =
        (fun v => v*upperEnvelope n v-upperEnvelope n v) := by funext v; ring
    rw [he, integral_sub (upperEnvelope_weighted_integrable n) (upperEnvelope_integrable n)]
    rfl
  linarith only [hrec]

/-- The total excess approaches exactly two from above, at a verified rate. -/
theorem mass_bounds (n : ℕ) :
    2 ≤ mass n ∧ mass n ≤ 2+24000*(19/20 : ℝ)^n := by
  rw [mass_eq_moment_difference]
  constructor
  · linarith only [firstMoment_succ_le n]
  · linarith only [firstMoment_difference_le n]

noncomputable def lowerProfile (n : ℕ) (s : ℝ) : ℝ :=
  1-tailIntegral (upperEnvelope n) (s-1)/s

lemma tailIntegral_upperEnvelope_le_mass (n : ℕ) (s : ℝ) (hs : 2 ≤ s) :
    tailIntegral (upperEnvelope n) (s-1) ≤ mass n := by
  apply setIntegral_mono_set (upperEnvelope_integrable n)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact upperEnvelope_nonneg n t (mem_Ioi.mp ht).le
  · exact Eventually.of_forall (fun t ht => by
      change 1 < t
      change s-1 < t at ht
      linarith)

theorem lowerProfile_bound (n : ℕ) (s : ℝ) (hs : 2 ≤ s) :
    (s-2-24000*(19/20 : ℝ)^n)/s ≤ lowerProfile n s := by
  have ht := (tailIntegral_upperEnvelope_le_mass n s hs).trans (mass_bounds n).2
  have hs0 : 0 < s := by linarith
  have hh := div_le_div_of_nonneg_right ht hs0.le
  unfold lowerProfile
  have he : (s-2-24000*(19/20 : ℝ)^n)/s = 1-(2+24000*(19/20 : ℝ)^n)/s := by
    field_simp
    ring
  rw [he]
  linarith only [hh]

/-- A single finite refinement depth works uniformly on every fixed half-line
s>=2+epsilon. The depth depends on epsilon, not on s. -/
theorem exists_depth_uniform_positive (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ∀ s : ℝ, 2+ε ≤ s → ε/(2*s) ≤ lowerProfile n s := by
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one
    (show (0 : ℝ) < ε/48000 by positivity) (by norm_num : (19/20 : ℝ) < 1)
  refine ⟨n,fun s hs => ?_⟩
  have hs2 : 2 ≤ s := by linarith
  have hs0 : 0 < s := by linarith
  apply le_trans _ (lowerProfile_bound n s hs2)
  have hp : 24000*(19/20 : ℝ)^n ≤ ε/2 := by linarith only [hn]
  apply (div_le_div_iff₀ (by positivity : 0 < 2*s) hs0).mpr
  nlinarith only [hp,hs,hs0]

theorem exists_depth_positive (s : ℝ) (hs : 2 < s) :
    ∃ n : ℕ, 0 < lowerProfile n s := by
  obtain ⟨n,hn⟩ := exists_depth_uniform_positive (s-2) (by linarith)
  refine ⟨n,lt_of_lt_of_le ?_ (hn s (by linarith))⟩
  exact div_pos (by linarith) (by linarith)

/-- This method does not supply positivity at the critical endpoint. -/
theorem lowerProfile_two_nonpos (n : ℕ) : lowerProfile n 2 ≤ 0 := by
  have hh := (mass_bounds n).1
  change 1-tailIntegral (upperEnvelope n) (2-1)/2 ≤ 0
  norm_num only [show (2 : ℝ)-1=1 by norm_num]
  change 1-mass n/2 ≤ 0
  linarith only [hh]

theorem clamped_lowerProfile_two (n : ℕ) : max 0 (lowerProfile n 2) = 0 :=
  max_eq_left (lowerProfile_two_nonpos n)

#print axioms mass_bounds
#print axioms exists_depth_uniform_positive
#print axioms clamped_lowerProfile_two
end Erdos970.ContinuousBuchstab
