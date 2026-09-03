import Submission.MovingWindowRoundingExplore

/-! Uniform moving-window logarithmic averages for the explicitly rounded
infinite set. The pointwise conjecture is not proved here. -/
namespace Erdos66MovingWindowLimit
open AdditiveCombinatorics Erdos66Fractional Erdos66Rounding
  Erdos66MovingWindowRounding Filter
open scoped Topology Classical
set_option maxHeartbeats 1200000

lemma log_atTop_nat : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

lemma moving_error_limit (w : ℕ → ℕ) (hw : ∀ᶠ n in atTop, w n ≤ n ∧ n ≤ (w n)^2) :
    Tendsto (fun n : ℕ ↦
      (∑ k∈movingWindow n (w n), ((sumRep (roundedSet profile) k : ℝ)-(harmonic (k+1) : ℝ)))/
        ((w n : ℝ)*Real.log n)) atTop (𝓝 0) := by
  have hinv := log_atTop_nat.const_div_atTop 1
  have hbound : Tendsto (fun n : ℕ ↦ 200*(1+Real.log 5+Real.log n)/(Real.log n)^2) atTop (𝓝 0) := by
    have hh := (hinv.add ((hinv.pow 2).const_mul (1+Real.log 5))).const_mul 200
    simp only [zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hlog : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hn))
    field_simp
    <;> ring
  have hsq : Tendsto (fun n : ℕ ↦
      ((∑ k∈movingWindow n (w n), ((sumRep (roundedSet profile) k : ℝ)-(harmonic (k+1) : ℝ)))/
        ((w n : ℝ)*Real.log n))^2) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n ↦ sq_nonneg _)) _ hbound
    filter_upwards [eventually_ge_atTop 2,hw] with n hn hw
    exact normalized_moving_error_sq hn hw.1 hw.2
  have habs := hsq.sqrt
  simp only [Real.sqrt_zero,Real.sqrt_sq_eq_abs] at habs
  exact (tendsto_zero_iff_abs_tendsto_zero _).mpr habs

lemma moving_harmonic_limit (w : ℕ → ℕ) (hw : ∀ᶠ n in atTop, 0<w n ∧ w n ≤ n) :
    Tendsto (fun n : ℕ ↦ (∑ k∈movingWindow n (w n), (harmonic (k+1) : ℝ))/
      ((w n : ℝ)*Real.log n)) atTop (𝓝 1) := by
  have hhi := (log_atTop_nat.const_div_atTop (1+Real.log 3)).const_add 1
  simp only [add_zero] at hhi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' harmonic_shift_log_ratio hhi
  · filter_upwards [eventually_ge_atTop 2,hw] with n hn hw
    have hW : (0 : ℝ)<w n := by exact_mod_cast hw.1
    have hlog : 0<Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    have hh := (moving_harmonic_bounds n (w n)).1
    apply (div_le_div_iff₀ hlog (mul_pos hW hlog)).mpr
    nlinarith
  · filter_upwards [eventually_ge_atTop 2,hw] with n hn hw
    have hW : (0 : ℝ)<w n := by exact_mod_cast hw.1
    have hlog : 0<Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    have hupper := moving_harmonic_upper (show 1 ≤ n by omega) hw.2
    have hm := mul_le_mul_of_nonneg_left hupper hW.le
    have hh := (moving_harmonic_bounds n (w n)).2.trans hm
    apply (div_le_iff₀ (mul_pos hW hlog)).mpr
    have he : (1+(1+Real.log 3)/Real.log n)*((w n : ℝ)*Real.log n)=
        (w n : ℝ)*(1+Real.log 3+Real.log n) := by
      field_simp
      <;> ring
    rw [he]
    exact hh

/-- The quantitative cumulative bound permits widths shorter than sqrt(n):
the sufficient condition is n/(w(n)^2 log n) -> 0. -/
lemma moving_error_limit_of_width (w : ℕ → ℕ)
    (hw : ∀ᶠ n in atTop, 0<w n ∧ w n ≤ n)
    (hscale : Tendsto (fun n : ℕ ↦ (n : ℝ)/((w n : ℝ)^2*Real.log n)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦
      (∑ k∈movingWindow n (w n), ((sumRep (roundedSet profile) k : ℝ)-(harmonic (k+1) : ℝ)))/
        ((w n : ℝ)*Real.log n)) atTop (𝓝 0) := by
  have hfactor : Tendsto (fun n : ℕ ↦ (1+Real.log 5+Real.log n)/Real.log n) atTop (𝓝 1) := by
    have hh := (log_atTop_nat.const_div_atTop (1+Real.log 5)).add_const 1
    simp only [zero_add] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hlog : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hn))
    field_simp
  have hbound := (hscale.mul hfactor).const_mul 200
  simp only [zero_mul,mul_zero] at hbound
  have hsq : Tendsto (fun n : ℕ ↦
      ((∑ k∈movingWindow n (w n), ((sumRep (roundedSet profile) k : ℝ)-(harmonic (k+1) : ℝ)))/
        ((w n : ℝ)*Real.log n))^2) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n ↦ sq_nonneg _)) _ hbound
    filter_upwards [eventually_ge_atTop 2,hw] with n hn hw
    have he := rounded_moving_error_sq (show 1 ≤ n by omega) hw.2
    have hlog : 0<Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    have hW : (0 : ℝ)<w n := by exact_mod_cast hw.1
    have hden : 0<((w n : ℝ)*Real.log n)^2 := sq_pos_of_pos (mul_pos hW hlog)
    rw [div_pow]
    apply (div_le_iff₀ hden).mpr
    have hid : 200*((n : ℝ)/((w n : ℝ)^2*Real.log n)*
        ((1+Real.log 5+Real.log n)/Real.log n))*((w n : ℝ)*Real.log n)^2 =
          200*(n : ℝ)*(1+Real.log 5+Real.log n) := by
      field_simp
      <;> ring
    rw [hid]
    exact he
  have habs := hsq.sqrt
  simp only [Real.sqrt_zero,Real.sqrt_sq_eq_abs] at habs
  exact (tendsto_zero_iff_abs_tendsto_zero _).mpr habs

/-- A general uniform moving-window averaged limit, still not pointwise. -/
theorem rounded_moving_window_limit_of_width (w : ℕ → ℕ)
    (hw : ∀ᶠ n in atTop, 0<w n ∧ w n ≤ n)
    (hscale : Tendsto (fun n : ℕ ↦ (n : ℝ)/((w n : ℝ)^2*Real.log n)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ (∑ k∈movingWindow n (w n), (sumRep (roundedSet profile) k : ℝ))/
      ((w n : ℝ)*Real.log n)) atTop (𝓝 1) := by
  have hh := (moving_harmonic_limit w hw).add (moving_error_limit_of_width w hw hscale)
  simp only [add_zero] at hh
  apply hh.congr
  intro n
  rw [Finset.sum_sub_distrib]
  ring

/-- One fixed infinite rounded set works for every width function between
sqrt(n) and n, with bounds interpreted eventually. -/
theorem rounded_moving_window_limit (w : ℕ → ℕ)
    (hw : ∀ᶠ n in atTop, w n ≤ n ∧ n ≤ (w n)^2) :
    Tendsto (fun n : ℕ ↦ (∑ k∈movingWindow n (w n), (sumRep (roundedSet profile) k : ℝ))/
      ((w n : ℝ)*Real.log n)) atTop (𝓝 1) := by
  have hw' : ∀ᶠ n in atTop, 0<w n ∧ w n ≤ n := by
    filter_upwards [eventually_ge_atTop 1,hw] with n hn hw
    exact ⟨by nlinarith [hw.2],hw.1⟩
  have hh := (moving_harmonic_limit w hw').add (moving_error_limit w hw)
  simp only [add_zero] at hh
  apply hh.congr
  intro n
  rw [Finset.sum_sub_distrib]
  ring

/-- Explicit moving windows of width floor(sqrt(n))+1. This is an averaged
analogue, not the pointwise limit required in Spec.lean. -/
theorem rounded_sqrt_window_limit :
    Tendsto (fun n : ℕ ↦
      (∑ k∈Finset.Ico (n+1) (n+Nat.sqrt n+2), (sumRep (roundedSet profile) k : ℝ))/
        (((Nat.sqrt n+1 : ℕ) : ℝ)*Real.log n)) atTop (𝓝 1) := by
  have hw : ∀ᶠ n in atTop, Nat.sqrt n+1 ≤ n ∧ n ≤ (Nat.sqrt n+1)^2 := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    exact ⟨by have := Nat.sqrt_lt_self (show 1<n by omega); omega,
      (Nat.le_succ n).trans (Nat.succ_le_succ_sqrt' n)⟩
  have hh := rounded_moving_window_limit (fun n ↦ Nat.sqrt n+1) hw
  convert hh using 1

end Erdos66MovingWindowLimit
