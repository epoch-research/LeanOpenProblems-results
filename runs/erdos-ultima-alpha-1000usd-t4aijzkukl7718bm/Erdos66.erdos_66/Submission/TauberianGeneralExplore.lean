import Submission.TauberianProfileExplore

/-! A direct Tauberian transfer for a nonnegative indicator series with the
square-root/logarithmic generating profile. -/
namespace Erdos66TauberianGeneral
open Filter AdditiveCombinatorics Erdos66Generating Erdos66TauberianTests
  Erdos66TauberianProfile Erdos66Counting
open scoped Topology

lemma generating_profile_power_ratio {A : Set ℕ} {d : ℝ} (hd : d ≠ 0)
    (h : Tendsto (fun r : ℝ ↦ series (indicator A) r * Real.sqrt (kernel r))
      (𝓝[<] 1) (𝓝 d)) (k : ℕ) (hk : k ≠ 0) :
    Tendsto (fun r : ℝ ↦ series (indicator A) (r ^ k) / series (indicator A) r)
      (𝓝[<] 1) (𝓝 (1 / Real.sqrt (k : ℝ))) := by
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hNk := h.comp (power_tendsto_one_left k hk)
  have hquot := hNk.div h hd
  simp only [Function.comp_def, div_self hd] at hquot
  have hh := hquot.div (power_kernel_ratio k hk).sqrt (Real.sqrt_ne_zero'.mpr hkpos)
  apply hh.congr'
  filter_upwards [unit_interval_eventually] with r hr
  have hw : 0 < kernel r := kernel_pos hr.1 hr.2
  have hwk : 0 < kernel (r ^ k) := kernel_pos (pow_pos hr.1 k) (pow_lt_one₀ hr.1.le hr.2 hk)
  dsimp only [Pi.div_apply]
  rw [Real.sqrt_div hwk.le]
  by_cases hF : series (indicator A) r = 0
  · simp only [hF, zero_mul, div_zero, zero_div]
  · have hs := Real.sqrt_ne_zero'.mpr hw
    have hsk := Real.sqrt_ne_zero'.mpr hwk
    field_simp

lemma series_ne_zero_of_profile {A : Set ℕ} {d : ℝ} (hd : d ≠ 0)
    (h : Tendsto (fun r : ℝ ↦ series (indicator A) r * Real.sqrt (kernel r))
      (𝓝[<] 1) (𝓝 d)) : ∀ᶠ r : ℝ in 𝓝[<] 1, series (indicator A) r ≠ 0 := by
  filter_upwards [h.eventually (eventually_ne_nhds hd)] with r hr
  exact (mul_ne_zero_iff.mp hr).1

/-- The needed Karamata-type conclusion is proved from polynomial tests and
continuous cutoffs, rather than assumed as an external Tauberian theorem. -/
theorem counting_profile_of_generating_profile {A : Set ℕ} {d : ℝ} (hd : d ≠ 0)
    (h : Tendsto (fun r : ℝ ↦ series (indicator A) r * Real.sqrt (kernel r))
      (𝓝[<] 1) (𝓝 d)) :
    Tendsto (fun N ↦ (count A N : ℝ) / Real.sqrt ((N : ℝ) * Real.log N)) atTop
      (𝓝 (2 * d / Real.sqrt Real.pi)) := by
  have hTests := continuous_test_limit_of_moments (generating_profile_power_ratio hd h)
  have hC := count_series_ratio_limit_of_tests hTests
  have hF := series_radius_limit_of_generating_limit h
  have hh := hC.mul hF
  have he : (2 / Real.sqrt Real.pi) * d = 2 * d / Real.sqrt Real.pi := by ring
  rw [he] at hh
  apply hh.congr'
  filter_upwards [radius_tendsto.eventually (series_ne_zero_of_profile hd h)] with N hN
  field_simp

end Erdos66TauberianGeneral
