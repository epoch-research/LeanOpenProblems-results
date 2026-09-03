import Submission.PrefixAbelComparisonExplore

/-! A fixed additive upper cap is incompatible with both a vanishing signed
prefix mean and a nonzero logarithmic representation limit. This only
excludes a restricted selection rule, not the original conjecture. -/
namespace Erdos66SharpCapRoundingObstruction
open Filter AdditiveCombinatorics Erdos66Generating Erdos66Fractional
  Erdos66Rounding Erdos66CumulativeRoundingError Erdos66AbelErrorEnergy
  Erdos66OneSidedMoment Erdos66PrefixAbelComparison Erdos66FractionalFourthPower
open scoped Topology Classical
set_option maxHeartbeats 1500000

lemma harmonic_error_log_limit {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n:ℝ)/Real.log n) atTop (𝓝 c)) :
    Tendsto (fun n ↦ ((sumRep A n:ℝ)-c*(harmonic (n+1):ℝ))/Real.log n)
      atTop (𝓝 0) := by
  have hh := h.sub (harmonic_shift_log_ratio.const_mul c)
  simp only [mul_one,sub_self] at hh
  convert hh using 1
  funext n
  ring

/-- A witness whose signed harmonic-centered prefix means tend to zero
cannot have a globally bounded upper error. -/
theorem no_bounded_upper_error {A : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n:ℝ)/Real.log n) atTop (𝓝 c))
    (hm : Tendsto (fun n ↦
      prefixSum (fun i ↦ (sumRep A i:ℝ)-c*(harmonic (i+1):ℝ)) n / ((n:ℝ)+1))
      atTop (𝓝 0)) :
    ¬ ∃ K : ℝ, ∀ n, (sumRep A n:ℝ)-c*(harmonic (n+1):ℝ) ≤ K := by
  rintro ⟨K,hK⟩
  have hcpos := Erdos66Explore.limit_pos hc h
  have hmoment := second_moment_limit_of_one_sided_bound
    (fun n ↦ (sumRep A n:ℝ)-c*(harmonic (n+1):ℝ)) (max 0 K) (le_max_left _ _)
    (fun n ↦ (hK n).trans (le_max_right _ _)) (harmonic_error_log_limit h) hm
  have hab := abel_zero_of_prefix_limit (errorSq A c) (fun n ↦ sq_nonneg _) hmoment
    (fun r hr0 hr1 ↦ summable_errorSq A c hr0.le hr1)
  have hsmall := hab.eventually_lt_const (half_pos hcpos)
  have hlarge := normalized_error_energy_eventually_gt hc h (by linarith : c/2 < c)
  obtain ⟨r,hr,hr'⟩ := (hsmall.and hlarge).exists
  linarith

/-- The analogous assertion for a globally bounded lower error. -/
theorem no_bounded_lower_error {A : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n:ℝ)/Real.log n) atTop (𝓝 c))
    (hm : Tendsto (fun n ↦
      prefixSum (fun i ↦ (sumRep A i:ℝ)-c*(harmonic (i+1):ℝ)) n / ((n:ℝ)+1))
      atTop (𝓝 0)) :
    ¬ ∃ K : ℝ, ∀ n, K ≤ (sumRep A n:ℝ)-c*(harmonic (n+1):ℝ) := by
  rintro ⟨K,hK⟩
  have hcpos := Erdos66Explore.limit_pos hc h
  let e : ℕ → ℝ := fun n ↦ -((sumRep A n:ℝ)-c*(harmonic (n+1):ℝ))
  have helim : Tendsto (fun n ↦ e n/Real.log n) atTop (𝓝 0) := by
    simpa only [e,neg_div,neg_zero] using (harmonic_error_log_limit h).neg
  have hemean : Tendsto (fun n ↦ prefixSum e n/((n:ℝ)+1)) atTop (𝓝 0) := by
    simpa only [e,prefixSum,Finset.sum_neg_distrib,neg_div,neg_zero] using hm.neg
  have hmoment := second_moment_limit_of_one_sided_bound e (max 0 (-K))
    (le_max_left _ _) (fun n ↦ (neg_le_neg (hK n)).trans (le_max_right _ _)) helim hemean
  have hsquare : (fun n ↦ (e n)^2) = errorSq A c := by
    funext n
    exact neg_sq _
  rw [hsquare] at hmoment
  have hab := abel_zero_of_prefix_limit (errorSq A c) (fun n ↦ sq_nonneg _) hmoment
    (fun r hr0 hr1 ↦ summable_errorSq A c hr0.le hr1)
  have hsmall := hab.eventually_lt_const (half_pos hcpos)
  have hlarge := normalized_error_energy_eventually_gt hc h (by linarith : c/2 < c)
  obtain ⟨r,hr,hr'⟩ := (hsmall.and hlarge).exists
  linarith

lemma global_upper_of_eventual (e : ℕ → ℝ) (K : ℝ)
    (h : ∀ᶠ n in atTop, e n ≤ K) : ∃ B : ℝ, ∀ n, e n ≤ B := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp h
  let D := ∑ i ∈ Finset.range N, |e i|
  have hD : 0 ≤ D := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
  refine ⟨max 0 K + D, fun n ↦ ?_⟩
  by_cases hn : N ≤ n
  · exact (hN n hn).trans ((le_max_right 0 K).trans (le_add_of_nonneg_right hD))
  · have hd : |e n| ≤ D := Finset.single_le_sum (f := fun i ↦ |e i|)
      (fun _ _ ↦ abs_nonneg _) (Finset.mem_range.mpr (by omega))
    exact (le_abs_self _).trans (hd.trans (le_add_of_nonneg_left (le_max_left _ _)))

theorem upper_error_frequently_large {A : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n:ℝ)/Real.log n) atTop (𝓝 c))
    (hm : Tendsto (fun n ↦
      prefixSum (fun i ↦ (sumRep A i:ℝ)-c*(harmonic (i+1):ℝ)) n / ((n:ℝ)+1))
      atTop (𝓝 0)) (K : ℝ) :
    ∃ᶠ n in atTop, K < (sumRep A n:ℝ)-c*(harmonic (n+1):ℝ) := by
  change ¬ (∀ᶠ n in atTop, ¬ K < (sumRep A n:ℝ)-c*(harmonic (n+1):ℝ))
  intro hnot
  apply no_bounded_upper_error hc h hm
  apply global_upper_of_eventual _ K
  simpa only [not_lt] using hnot

lemma profile_tendsto_zero : Tendsto profile atTop (𝓝 0) := by
  have hh := (summable_profile_fourth.tendsto_atTop_zero.sqrt).sqrt
  simp only [Real.sqrt_zero] at hh
  convert hh using 1
  funext n
  have hp := profile_nonneg n
  rw [show (profile n)^4 = ((profile n)^2)^2 by ring,
    Real.sqrt_sq (sq_nonneg _), Real.sqrt_sq hp]

lemma profile_prefix_mean_zero :
    Tendsto (fun n ↦ prefixSum profile n/((n:ℝ)+1)) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ ↦ n+1) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ Nat.le_succ n) tendsto_id
  have hh := profile_tendsto_zero.cesaro.comp hn
  simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one,prefixSum,
    div_eq_mul_inv,mul_comm] using hh

lemma balanced_representation_mean_zero (A : Set ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hbal : ∀ n, |prefixSum (roundingError A) n| ≤ D) :
    Tendsto (fun n ↦
      prefixSum (fun i ↦ (sumRep A i:ℝ)-(harmonic (i+1):ℝ)) n/((n:ℝ)+1))
      atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ ↦ (n:ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ le_add_of_nonneg_right zero_le_one)
      tendsto_natCast_atTop_atTop
  have hlim := ((profile_prefix_mean_zero.const_mul 2).add
    (hn.const_div_atTop D)).const_mul D
  simp only [mul_zero,add_zero] at hlim
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply squeeze_zero' (Eventually.of_forall (fun n ↦ abs_nonneg _)) _ hlim
  filter_upwards [] with n
  have hb := representation_prefix_error A D hD hbal n
  rw [abs_div,abs_of_pos (by positivity : 0 < (n:ℝ)+1)]
  have hh := div_le_div_of_nonneg_right hb (by positivity : 0 ≤ (n:ℝ)+1)
  convert hh using 1
  ring

lemma limit_eq_one_of_small_signed_mean {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n:ℝ)/Real.log n) atTop (𝓝 c))
    (hm : Tendsto (fun n ↦
      prefixSum (fun i ↦ (sumRep A i:ℝ)-(harmonic (i+1):ℝ)) n/((n:ℝ)+1))
      atTop (𝓝 0)) : c = 1 := by
  have hn : Tendsto (fun n : ℕ ↦ n+1) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ Nat.le_succ n) tendsto_id
  have he : Tendsto (fun n ↦ ((sumRep A n:ℝ)-(harmonic (n+1):ℝ))/Real.log n)
      atTop (𝓝 (c-1)) := by
    simpa only [sub_div] using h.sub harmonic_shift_log_ratio
  have hcumul := (Erdos66Cumulative.cumulative_of_log_limit he).comp hn
  have hlog : Tendsto (fun n : ℕ ↦ Real.log ((n:ℝ)+1)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_mono
      (fun n ↦ le_add_of_nonneg_right zero_le_one) tendsto_natCast_atTop_atTop)
  have hz := hm.div_atTop hlog
  have hzero : Tendsto (fun n : ℕ ↦
      (∑ i ∈ Finset.range (n+1), ((sumRep A i:ℝ)-(harmonic (i+1):ℝ))) /
        (((n:ℝ)+1)*Real.log ((n:ℝ)+1))) atTop (𝓝 0) := by
    simpa only [prefixSum,div_div] using hz
  have hother : Tendsto (fun n : ℕ ↦
      (∑ i ∈ Finset.range (n+1), ((sumRep A i:ℝ)-(harmonic (i+1):ℝ))) /
        (((n:ℝ)+1)*Real.log ((n:ℝ)+1))) atTop (𝓝 (c-1)) := by
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using hcumul
  have := tendsto_nhds_unique hother hzero
  linarith

/-- No bounded-discrepancy harmonic rounding can both have limit one and
stay eventually below the harmonic center plus a fixed additive constant. -/
theorem bounded_rounding_sharp_cap_no_limit (A : Set ℕ) (D K : ℝ) (hD : 0 ≤ D)
    (hbal : ∀ n, |prefixSum (roundingError A) n| ≤ D)
    (hcap : ∀ᶠ n in atTop, (sumRep A n:ℝ) ≤ (harmonic (n+1):ℝ)+K) :
    ¬ Tendsto (fun n ↦ (sumRep A n:ℝ)/Real.log n) atTop (𝓝 1) := by
  intro h
  have hm := balanced_representation_mean_zero A D hD hbal
  apply no_bounded_upper_error one_ne_zero h (by simpa only [one_mul] using hm)
  apply global_upper_of_eventual _ K
  filter_upwards [hcap] with n hn
  simp only [one_mul]
  linarith

/-- The coefficient cannot be changed to evade this restricted-class obstruction. -/
theorem bounded_rounding_sharp_cap_no_finite_limit (A : Set ℕ) (D K : ℝ)
    (hD : 0 ≤ D) (hbal : ∀ n, |prefixSum (roundingError A) n| ≤ D)
    (hcap : ∀ᶠ n in atTop, (sumRep A n:ℝ) ≤ (harmonic (n+1):ℝ)+K) (c : ℝ) :
    ¬ Tendsto (fun n ↦ (sumRep A n:ℝ)/Real.log n) atTop (𝓝 c) := by
  intro h
  have hc := limit_eq_one_of_small_signed_mean h
    (balanced_representation_mean_zero A D hD hbal)
  subst c
  exact bounded_rounding_sharp_cap_no_limit A D K hD hbal hcap h

end Erdos66SharpCapRoundingObstruction
