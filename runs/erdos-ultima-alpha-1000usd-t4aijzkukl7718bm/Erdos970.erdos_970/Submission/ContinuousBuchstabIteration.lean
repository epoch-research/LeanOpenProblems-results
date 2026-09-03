import Submission.ContinuousBuchstabMoments

/-! Finite iterates of the continuous Buchstab model. The exponential kernel
estimate gives a quantitative bound for consecutive differences. -/
namespace Erdos970.ContinuousBuchstab
open Real Set Filter MeasureTheory
open scoped Topology
set_option maxHeartbeats 1000000

noncomputable def forcing (s : ℝ) : ℝ := max (3-s) 0/s

lemma measurable_forcing : Measurable forcing :=
  ((measurable_const.sub measurable_id).max measurable_const).div measurable_id

lemma forcing_nonneg (s : ℝ) (hs : 1 ≤ s) : 0 ≤ forcing s :=
  div_nonneg (le_max_right _ _) (by linarith)

lemma forcing_le_two (s : ℝ) (hs : 1 ≤ s) : forcing s ≤ 2 := by
  unfold forcing
  apply (div_le_iff₀ (by linarith : 0 < s)).mpr
  apply max_le <;> linarith

lemma forcing_exp_envelope (s : ℝ) (hs : 1 ≤ s) :
    |forcing s| ≤ 100*exp (-s) := by
  rw [abs_of_nonneg (forcing_nonneg s hs)]
  by_cases h3 : 3 ≤ s
  · have he : forcing s = 0 := by simp only [forcing, max_eq_right (by linarith : 3-s ≤ 0), zero_div]
    rw [he]
    positivity
  · have hE : exp s ≤ 27 := by
      have h1 := exp_one_lt_three
      have he : exp 3 = (exp 1)^3 := by rw [← exp_nat_mul]; norm_num
      apply (exp_le_exp.mpr (by linarith : s ≤ 3)).trans
      rw [he]
      nlinarith [exp_pos (1 : ℝ), sq_nonneg (exp 1-3)]
    have hh := mul_le_mul (forcing_le_two s hs) hE (exp_pos s).le (by norm_num : (0 : ℝ) ≤ 2)
    have hm := mul_le_mul_of_nonneg_right hh (exp_pos (-s)).le
    have he : exp s*exp (-s) = 1 := by rw [← exp_add]; simp
    rw [mul_assoc,he,mul_one] at hm
    have hp := exp_pos (-s)
    nlinarith only [hm,hp]

noncomputable def upperEnvelope : ℕ → ℝ → ℝ
  | 0 => fun s => 2000*exp (-s)
  | n+1 => fun s => forcing s+kernel (upperEnvelope n) s

lemma measurable_upperEnvelope (n : ℕ) : Measurable (upperEnvelope n) := by
  induction n with
  | zero => exact measurable_const.mul (Real.measurable_exp.comp measurable_neg)
  | succ n ih => exact measurable_forcing.add (measurable_kernel _ ih)

lemma upperEnvelope_nonneg (n : ℕ) (s : ℝ) (hs : 1 ≤ s) : 0 ≤ upperEnvelope n s := by
  induction n generalizing s with
  | zero => dsimp [upperEnvelope]; positivity
  | succ n ih => exact add_nonneg (forcing_nonneg s hs) (kernel_nonneg _ ih s hs)

lemma upperEnvelope_exp_bound (n : ℕ) (s : ℝ) (hs : 1 ≤ s) :
    |upperEnvelope n s| ≤ 2000*exp (-s) := by
  induction n generalizing s with
  | zero => dsimp [upperEnvelope]; rw [abs_of_pos (by positivity : 0 < 2000*exp (-s))]
  | succ n ih =>
      have hk := kernel_abs_le_exp (upperEnvelope n) (measurable_upperEnvelope n) 2000
        (by norm_num) ih s hs
      have hg := forcing_exp_envelope s hs
      have hh := abs_add_le (forcing s) (kernel (upperEnvelope n) s)
      change |forcing s+kernel (upperEnvelope n) s| ≤ _
      linarith only [hk,hg,hh]

lemma upperEnvelope_succ_le (n : ℕ) (s : ℝ) (hs : 1 ≤ s) :
    upperEnvelope (n+1) s ≤ upperEnvelope n s := by
  induction n generalizing s with
  | zero =>
      exact (le_abs_self _).trans (upperEnvelope_exp_bound 1 s hs)
  | succ n ih =>
      have hh := kernel_mono (upperEnvelope (n+1)) (upperEnvelope n)
        (measurable_upperEnvelope _) (measurable_upperEnvelope _) 2000 2000
        (upperEnvelope_exp_bound _) (upperEnvelope_exp_bound _) ih s hs
      change forcing s+kernel (upperEnvelope (n+1)) s ≤ forcing s+kernel (upperEnvelope n) s
      linarith only [hh]

/-- Consecutive upper envelopes decrease at a uniform geometric rate. -/
theorem upperEnvelope_difference_bound (n : ℕ) (s : ℝ) (hs : 1 ≤ s) :
    |upperEnvelope n s-upperEnvelope (n+1) s| ≤
      (2000*(19/20 : ℝ)^n)*exp (-s) := by
  induction n generalizing s with
  | zero =>
      rw [abs_of_nonneg (sub_nonneg.mpr (upperEnvelope_succ_le 0 s hs))]
      have hpos := upperEnvelope_nonneg 1 s hs
      simp only [upperEnvelope, pow_zero, mul_one] at *
      linarith only [hpos]
  | succ n ih =>
      have hh := kernel_abs_le_exp
        (fun t => upperEnvelope n t-upperEnvelope (n+1) t)
        ((measurable_upperEnvelope n).sub (measurable_upperEnvelope (n+1)))
        (2000*(19/20 : ℝ)^n) (by positivity) ih s hs
      rw [kernel_sub (upperEnvelope n) (upperEnvelope (n+1))
        (measurable_upperEnvelope _) (measurable_upperEnvelope _) 2000 2000
        (upperEnvelope_exp_bound _) (upperEnvelope_exp_bound _)] at hh
      have he : upperEnvelope (n+1) s-upperEnvelope (n+1+1) s =
          kernel (upperEnvelope n) s-kernel (upperEnvelope (n+1)) s := by
        change (forcing s+kernel (upperEnvelope n) s)-(forcing s+kernel (upperEnvelope (n+1)) s) = _
        ring
      rw [he]
      simpa only [pow_succ, mul_assoc] using hh

noncomputable def mass (n : ℕ) : ℝ := ∫ s : ℝ in Ioi 1, upperEnvelope n s
noncomputable def firstMoment (n : ℕ) : ℝ := ∫ s : ℝ in Ioi 1, s*upperEnvelope n s

lemma upperEnvelope_integrable (n : ℕ) : IntegrableOn (upperEnvelope n) (Ioi 1) :=
  integrable_of_exp_envelope _ (measurable_upperEnvelope n) 2000 1 (upperEnvelope_exp_bound n) le_rfl

lemma upperEnvelope_weighted_integrable (n : ℕ) :
    IntegrableOn (fun s => s*upperEnvelope n s) (Ioi 1) :=
  integrable_weighted_envelope _ (measurable_upperEnvelope n) 2000 (upperEnvelope_exp_bound n)

lemma firstMoment_succ_le (n : ℕ) : firstMoment (n+1) ≤ firstMoment n := by
  exact setIntegral_mono_on (upperEnvelope_weighted_integrable _) (upperEnvelope_weighted_integrable _)
    measurableSet_Ioi (fun s hs => mul_le_mul_of_nonneg_left
      (upperEnvelope_succ_le n s (mem_Ioi.mp hs).le) (by linarith [mem_Ioi.mp hs]))

lemma firstMoment_difference_le (n : ℕ) :
    firstMoment n-firstMoment (n+1) ≤ 24000*(19/20 : ℝ)^n := by
  have hh := setIntegral_mono_on
    ((upperEnvelope_weighted_integrable n).sub (upperEnvelope_weighted_integrable (n+1)))
    (integrable_linear_exp.const_mul (2000*(19/20 : ℝ)^n)) measurableSet_Ioi (fun s hs => by
      have hs1 := (mem_Ioi.mp hs).le
      have hs0 : 0 ≤ s := by linarith [mem_Ioi.mp hs]
      have hb := (le_abs_self _).trans (upperEnvelope_difference_bound n s hs1)
      have hm := mul_le_mul_of_nonneg_left hb hs0
      dsimp only [Pi.sub_apply]
      nlinarith only [hm])
  simp only [Pi.sub_apply] at hh
  rw [integral_sub (upperEnvelope_weighted_integrable n) (upperEnvelope_weighted_integrable (n+1)),
    integral_const_mul] at hh
  have hl := mul_le_mul_of_nonneg_left integral_linear_exp_le
    (show 0 ≤ 2000*(19/20 : ℝ)^n by positivity)
  change firstMoment n-firstMoment (n+1) ≤ _ at hh
  nlinarith only [hh,hl]

#print axioms upperEnvelope_difference_bound
#print axioms firstMoment_difference_le
end Erdos970.ContinuousBuchstab
