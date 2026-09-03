import Submission.SymmetricExposureTail
import Submission.FiveEighthTail
import Submission.ThirteenSixteenthPowerBound

/-!
An unconditional stretched-exponential bound for the covered phase fraction at
quadratic interval lengths. This is weaker than the critical exponential rate
needed to rule out every exceptional phase and does not settle Erdős 970.
-/
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Erdos970.GapAverages
open Finset Real Filter FiniteSelberg

lemma exposure_core_log_bound (D t b : ℕ) (ht : 0 < t)
    (hDt : 384 * (D + 1) ≤ t) (hb : b ≤ D * t ^ 10 + 1) :
    (b : ℝ) * log (1 + 4 * (t : ℝ) ^ 12) ≤ (t : ℝ) ^ 12 / 32 := by
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ) < t := by linarith
  have ht10 : (1 : ℝ) ≤ (t : ℝ) ^ 10 := one_le_pow₀ ht1
  have ht12 : (1 : ℝ) ≤ (t : ℝ) ^ 12 := one_le_pow₀ ht1
  have hlog0 : 0 ≤ log (1 + 4 * (t : ℝ) ^ 12) := log_nonneg (by nlinarith [pow_nonneg ht0.le 12])
  have hlog : log (1 + 4 * (t : ℝ) ^ 12) ≤ 12 * t := by
    have hh := log_le_log (by positivity : 0 < 1 + 4 * (t : ℝ) ^ 12)
      (show 1 + 4 * (t : ℝ) ^ 12 ≤ 5 * (t : ℝ) ^ 12 by nlinarith)
    rw [log_mul (by norm_num) (pow_ne_zero _ ht0.ne'), log_pow] at hh
    have h5 := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5)
    have hT := log_le_sub_one_of_pos ht0
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have hbR : (b : ℝ) ≤ ((D : ℝ) + 1) * (t : ℝ) ^ 10 := by
    have hh : (b : ℝ) ≤ (D : ℝ) * (t : ℝ) ^ 10 + 1 := by exact_mod_cast hb
    nlinarith
  have hscale : 384 * ((D : ℝ) + 1) ≤ t := by exact_mod_cast hDt
  have ha := mul_le_mul hbR hlog hlog0 (by positivity : 0 ≤ ((D : ℝ) + 1) * (t : ℝ) ^ 10)
  have hh := mul_le_mul_of_nonneg_right hscale (pow_nonneg ht0.le 11)
  have hp : (t : ℝ) ^ 12 = (t : ℝ) * (t : ℝ) ^ 11 := by ring
  nlinarith only [ha, hh, hp]

/-- The earlier 21/8 bound supplies the required exposure depth at quadratic
lengths after passage to a sixteenth-power cardinality envelope. -/
lemma quadratic_bound_at_exposure_depth (k t : ℕ) (hk : 0 < k) (ht : 0 < t)
    (htk : t ^ 16 ≤ 65536 * k)
    (hlarge : twentyOneEighthConstant * 2 ^ 21 * 65536 ^ 16 ≤ t) :
    IsJacobsthalBound (2 * t ^ 12 - 1) (k ^ 2) := by
  have hj : 0 < 2 * t ^ 12 - 1 := by
    have hh : 1 ≤ t ^ 12 := one_le_pow₀ ht
    omega
  have hh := jacobsthalFunction_eighth_le_twenty_first (2 * t ^ 12 - 1) hj
  have hidx := Nat.pow_le_pow_left (Nat.sub_le (2 * t ^ 12) 1) 21
  have hc : twentyOneEighthConstant * 2 ^ 21 * 65536 ^ 16 ≤ t ^ 4 :=
    hlarge.trans (Nat.le_pow (by omega))
  have hpow := Nat.pow_le_pow_left htk 16
  have hfinal : 65536 ^ 16 * jacobsthalFunction (2 * t ^ 12 - 1) ^ 8 ≤
      65536 ^ 16 * (k ^ 2) ^ 8 := by
    calc
      _ ≤ 65536 ^ 16 * (twentyOneEighthConstant * (2 * t ^ 12 - 1) ^ 21) :=
        Nat.mul_le_mul_left _ hh
      _ ≤ 65536 ^ 16 * (twentyOneEighthConstant * (2 * t ^ 12) ^ 21) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hidx)
      _ = (twentyOneEighthConstant * 2 ^ 21 * 65536 ^ 16) * t ^ 252 := by ring
      _ ≤ t ^ 4 * t ^ 252 := Nat.mul_le_mul_right _ hc
      _ = (t ^ 16) ^ 16 := by ring
      _ ≤ (65536 * k) ^ 16 := hpow
      _ = _ := by ring
  have hcancel : jacobsthalFunction (2 * t ^ 12 - 1) ^ 8 ≤ (k ^ 2) ^ 8 :=
    (mul_le_mul_iff_right₀ (by positivity : 0 < (65536 : ℕ) ^ 16)).mp hfinal
  apply (jacobsthalFunction_le_iff _ _).mp
  exact (Nat.pow_le_pow_iff_left (by omega : 8 ≠ 0)).mp hcancel

noncomputable def exposureThreshold : ℕ :=
  max (384 * (thirteenSixteenthCutoffScale + 1))
    (twentyOneEighthConstant * 2 ^ 21 * 65536 ^ 16)

lemma exposureThreshold_pos : 0 < exposureThreshold := by
  unfold exposureThreshold
  have hh := le_max_left (384 * (thirteenSixteenthCutoffScale + 1))
    (twentyOneEighthConstant * 2 ^ 21 * 65536 ^ 16)
  omega

/-- Explicit exposure estimate on one sixteenth-power envelope. -/
lemma quadratic_envelope_void (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (k t D : ℕ) (ht : 0 < t) (hPt : P.card ≤ t ^ 16)
    (hD1024 : 1024 ≤ D)
    (hlogD : 2048 * (WeightedMertens.boundConstant + 1) ≤ log (D : ℝ))
    (hDt : 384 * (D + 1) ≤ t) (hb : IsJacobsthalBound (2 * t ^ 12 - 1) (k ^ 2)) :
    coveredFraction P (k ^ 2) ≤ exp (-(t : ℝ) ^ 12 / 32) := by
  let S := P.filter (fun p => p ≤ D * t ^ 10)
  have hSP : S ⊆ P := filter_subset _ _
  have hScard : S.card ≤ D * t ^ 10 + 1 := by
    have hsub : S ⊆ range (D * t ^ 10 + 1) := by
      intro p hp
      exact mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp hp).2)
    simpa only [card_range] using card_le_card hsub
  have hhalf : (∑ p ∈ P \ S, (p : ℝ)⁻¹) ≤ 1 / 2 := by
    have he : P \ S = P.filter (fun p => D * t ^ 10 < p) := by
      apply Finset.ext
      intro p
      constructor
      · intro hp
        obtain ⟨hpP, hpS⟩ := Finset.mem_sdiff.mp hp
        apply mem_filter.mpr
        refine ⟨hpP, ?_⟩
        by_contra hn
        exact hpS (mem_filter.mpr ⟨hpP, le_of_not_gt hn⟩)
      · intro hp
        obtain ⟨hpP, hlt⟩ := mem_filter.mp hp
        apply Finset.mem_sdiff.mpr
        refine ⟨hpP, ?_⟩
        intro hpS
        exact hlt.not_ge (mem_filter.mp hpS).2
    rw [he]
    simpa only [one_div] using WeightedMertens.tail_five_eighths P hP t D ht hD1024 hlogD hPt
  have hprob := coveredFraction_le_core_exponential P S hP hSP (k ^ 2) (t ^ 12)
    (Nat.pow_pos ht) hb hhalf
  have hcost := exposure_core_log_bound D t S.card ht hDt hScard
  apply hprob.trans
  apply exp_le_exp.mpr
  push_cast
  linarith only [hcost]

lemma sixteenth_envelope_pos (A k : ℕ) (hA : 0 < A) (hk : A ^ 16 ≤ k) : 0 < k :=
  (Nat.pow_pos hA).trans_le hk

lemma sixteenth_envelope_threshold (A k t : ℕ) (hA : A ^ 16 ≤ k)
    (hkt : k ≤ t ^ 16) : A ≤ t :=
  (Nat.pow_le_pow_iff_left (by decide : 16 ≠ 0)).mp (hA.trans hkt)

lemma exposureThreshold_bounds {t : ℕ} (h : exposureThreshold ≤ t) :
    384 * (thirteenSixteenthCutoffScale + 1) ≤ t ∧
      twentyOneEighthConstant * 2 ^ 21 * 65536 ^ 16 ≤ t := by
  exact ⟨(le_max_left _ _).trans h, (le_max_right _ _).trans h⟩

lemma exposureCutoffScale_log :
    2048 * (WeightedMertens.boundConstant + 1) ≤ log (thirteenSixteenthCutoffScale : ℝ) := by
  have hh := thirteenSixteenthCutoffScale_log
  linarith only [hh, quadraticEnergyError_pos, WeightedMertens.boundConstant_pos]

lemma sixteenth_envelope_quarter (k t : ℕ) (hkt : k ≤ t ^ 16) :
    (k : ℝ) ^ ((3 : ℝ) / 4) ≤ (t : ℝ) ^ 12 := by
  have hh := rpow_le_rpow (Nat.cast_nonneg k)
    (show (k : ℝ) ≤ (t : ℝ) ^ 16 by exact_mod_cast hkt) (by norm_num : (0 : ℝ) ≤ 3 / 4)
  have he : ((t : ℝ) ^ 16) ^ ((3 : ℝ) / 4) = (t : ℝ) ^ 12 := by
    rw [← rpow_natCast (t : ℝ) 16, ← rpow_mul (Nat.cast_nonneg t)]
    norm_num
  rwa [he] at hh

/-- Every sufficiently large prime budget has a stretched-exponentially small
covered phase fraction at interval length k^2. This estimate is uniform over
all prime sets of cardinality at most k, with no cap on the primes. -/
theorem coveredFraction_quadratic_stretched (k : ℕ) (hk : exposureThreshold ^ 16 ≤ k)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hPk : P.card ≤ k) :
    coveredFraction P (k ^ 2) ≤ exp (-((k : ℝ) ^ ((3 : ℝ) / 4) / 32)) := by
  have hkpos : 0 < k := sixteenth_envelope_pos exposureThreshold k exposureThreshold_pos hk
  obtain ⟨t, ht, hkt, htk⟩ := exists_sixteenth_power_envelope k hkpos
  have hthreshold : exposureThreshold ≤ t :=
    sixteenth_envelope_threshold exposureThreshold k t hk hkt
  obtain ⟨hDt, hlarge⟩ := exposureThreshold_bounds hthreshold
  have hD1024 : 1024 ≤ thirteenSixteenthCutoffScale :=
    (by norm_num : 1024 ≤ 65536).trans thirteenSixteenthCutoffScale_ge
  have hlogD := exposureCutoffScale_log
  have hb := quadratic_bound_at_exposure_depth k t hkpos ht htk hlarge
  have hprob := quadratic_envelope_void P hP k t thirteenSixteenthCutoffScale ht
    (hPk.trans hkt) hD1024 hlogD hDt hb
  have hquarter := sixteenth_envelope_quarter k t hkt
  apply hprob.trans
  apply exp_le_exp.mpr
  linarith only [hquarter]

/-- Filter form of the same unconditional estimate. -/
theorem eventually_quadratic_stretched_void :
    ∀ᶠ k : ℕ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ k →
      coveredFraction P (k ^ 2) ≤ exp (-((k : ℝ) ^ ((3 : ℝ) / 4) / 32)) := by
  filter_upwards [eventually_ge_atTop (exposureThreshold ^ 16)] with k hk
  exact coveredFraction_quadratic_stretched k hk

/-- Scope of the estimate: at full cardinality its exponent is smaller than
the logarithm of the phase-space size. It therefore does not exclude a single
exceptional covered phase by the phase-counting argument alone. -/
lemma stretched_exponent_le_phase_entropy (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (k : ℕ) (hk : 0 < k) (hcard : P.card = k) :
    (k : ℝ) ^ ((3 : ℝ) / 4) / 32 ≤ ∑ p ∈ P, log (p : ℝ) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpow : (k : ℝ) ^ ((3 : ℝ) / 4) ≤ k := by
    simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hk1
      (by norm_num : (3 : ℝ) / 4 ≤ 1)
  have hlog : (1 : ℝ) / 32 ≤ log 2 := by linarith only [log_two_gt_d9]
  have he : (k : ℝ) * log 2 ≤ ∑ p ∈ P, log (p : ℝ) := by
    calc
      _ = ∑ _p ∈ P, log (2 : ℝ) := by simp [hcard]
      _ ≤ _ := by
        apply sum_le_sum
        intro p hp
        exact log_le_log (by norm_num) (by exact_mod_cast (hP p hp).two_le)
  have hh := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg k)
  linarith

#print axioms stretched_exponent_le_phase_entropy

#print axioms coveredFraction_quadratic_stretched
#print axioms eventually_quadratic_stretched_void
end Erdos970.GapAverages
