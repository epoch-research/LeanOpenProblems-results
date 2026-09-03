import Submission.PeriodicMixedDiscrepancyExplore

/-! A limitation of the generic residue-histogram error certificate.
The statements concern the size of that certificate, not actual mixed errors. -/
namespace Erdos66PeriodicMixResolution
open Filter
open scoped Topology
set_option maxHeartbeats 1600000

lemma budget_forces_small_scale (x m s C ε ℓ : ℝ)
    (hx : 0 ≤ x) (hm : 0 ≤ m) (hs : 1 ≤ s) (hC : 0 ≤ C) (hℓ : 0 ≤ ℓ)
    (hdensity : x*s^2  ≤  C*ℓ*m^2) (hbudget : m*s ≤ ε*ℓ) :
    x ≤ C*ε^2*ℓ^3 := by
  have hs0 : 0 ≤ s := by linarith
  have hss : 1 ≤ s^2 := by nlinarith
  have hm' : m ≤ ε*ℓ := by nlinarith
  have hεℓ : 0 ≤ ε*ℓ := hm.trans hm'
  have hm2 : m^2 ≤ (ε*ℓ)^2 := sq_le_sq₀ hm hεℓ |>.mpr hm'
  calc
    x  ≤  x*s^2 := by nlinarith
    _  ≤  C*ℓ*m^2 := hdensity
    _  ≤  C*ℓ*(ε*ℓ)^2 := mul_le_mul_of_nonneg_left hm2 (mul_nonneg hC hℓ)
    _ = C*ε^2*ℓ^3 := by ring

lemma log_cube_over_nat :
    Tendsto (fun n : ℕ ↦ (Real.log (n:ℝ))^3/(n:ℝ)) atTop (𝓝 0) := by
  have hh := ((isLittleO_log_rpow_rpow_atTop (3:ℝ) (by norm_num : (0:ℝ) < 1)).tendsto_div_nhds_zero).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [←Real.rpow_natCast,Real.rpow_one,Function.comp_def] using hh

lemma eventually_log_cube_lt (C ε : ℝ) :
    ∀ᶠ n : ℕ in atTop, C*ε^2*(Real.log (n:ℝ))^3 < (n:ℝ) := by
  have hh := log_cube_over_nat.const_mul (C*ε^2)
  simp only [mul_zero] at hh
  filter_upwards [hh.eventually_lt_const (by norm_num : (0:ℝ) < 1),
    eventually_ge_atTop 2] with n hn hn2
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have he : C*ε^2*((Real.log (n:ℝ))^3/(n:ℝ))=
      (C*ε^2*(Real.log (n:ℝ))^3)/(n:ℝ) := by ring
  rw [he] at hn
  simpa using (div_lt_iff₀ hn0).mp hn

/-- At logarithmic sparse density, even m*s already exceeds every fixed
multiple of log n, uniformly over the integer modulus and nonzero size. -/
theorem eventually_no_small_histogram_certificate (C ε : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop, ∀ m s : ℕ, 0 < m → 0 < s →
      (n:ℝ)*(s:ℝ)^2 ≤ C*Real.log (n:ℝ)*(m:ℝ)^2 →
      ε*Real.log (n:ℝ) < (m:ℝ)*s := by
  filter_upwards [eventually_log_cube_lt C ε,eventually_ge_atTop 2] with n hn hn2
  intro m s hm hs hdensity
  by_contra hbad
  have hs' : (1:ℝ) ≤ s := by exact_mod_cast hs
  have hℓ : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hh := budget_forces_small_scale n m s C ε (Real.log (n:ℝ))
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hs' hC hℓ hdensity (le_of_not_gt hbad)
  exact (not_le_of_gt hn) hh

/-- In particular the explicit phased-prefix bound cannot certify sublogarithmic
mixing at the target density merely by increasing the modulus. -/
theorem phased_certificate_too_large (C ε : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop, ∀ m s t : ℕ, 0 < m → 0 < s →
      (n:ℝ)*(s:ℝ)^2 ≤ C*Real.log (n:ℝ)*(m:ℝ)^2 →
      ε*Real.log (n:ℝ) < 2*((t:ℝ)+2)*m*s := by
  filter_upwards [eventually_no_small_histogram_certificate C ε hC] with n hn
  intro m s t hm hs hdensity
  have hh := hn m s hm hs hdensity
  have hb : (m:ℝ)*s ≤ 2*((t:ℝ)+2)*m*s := by
    have ht : 0 ≤ (t:ℝ) := Nat.cast_nonneg _
    have hm0 : 0 ≤ (m:ℝ) := Nat.cast_nonneg _
    have hs0 : 0 ≤ (s:ℝ) := Nat.cast_nonneg _
    have hp : 0 ≤ (m:ℝ)*s := mul_nonneg hm0 hs0
    nlinarith
  exact hh.trans_le hb

end Erdos66PeriodicMixResolution
