import Submission.QuadraticWindowRoundingExplore

/-! An unconditional averaged analogue for one infinite rounded set. No
pointwise logarithmic representation limit is claimed. -/
namespace Erdos66QuadraticWindowLimit
open AdditiveCombinatorics Erdos66Fractional Erdos66Rounding
  Erdos66CumulativeRoundingError Erdos66QuadraticWindowRounding Filter
open scoped Topology Classical
set_option maxHeartbeats 1500000

lemma square_log_atTop : Tendsto (fun n : ℕ ↦ Real.log (n^2 : ℕ)) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp (tendsto_pow_atTop (by decide : 2 ≠ 0)))

lemma square_log_pos {n : ℕ} (hn : 2 ≤ n) : 0<Real.log (n^2 : ℕ) :=
  Real.log_pos (by exact_mod_cast (show 1<n^2 by nlinarith))

lemma normalized_window_error_sq {n : ℕ} (hn : 2 ≤ n) :
    ((∑ k∈squareWindow n, ((sumRep (roundedSet profile) k : ℝ)-(harmonic (k+1) : ℝ)))/
      (((2*n+1 : ℕ) : ℝ)*Real.log (n^2 : ℕ)))^2 ≤
      400*(1+Real.log 9+Real.log (n^2 : ℕ))/(Real.log (n^2 : ℕ))^2 := by
  have he := rounded_window_error_sq (show 1 ≤ n by omega)
  have hW : (n : ℝ)^2 ≤ (((2*n+1 : ℕ) : ℝ))^2 := by push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hL : 0 ≤ 1+Real.log 9+Real.log (n^2 : ℕ) := by
    have h9 : 0 ≤ Real.log 9 := Real.log_nonneg (by norm_num)
    have hn0 := (square_log_pos hn).le
    linarith
  have hm := mul_le_mul_of_nonneg_left hW (by positivity : 0 ≤ 400*(1+Real.log 9+Real.log (n^2 : ℕ)))
  have hb : (∑ k∈squareWindow n, ((sumRep (roundedSet profile) k : ℝ)-(harmonic (k+1) : ℝ)))^2 ≤
      (400*(1+Real.log 9+Real.log (n^2 : ℕ)))*(((2*n+1 : ℕ) : ℝ))^2 := by nlinarith
  rw [div_pow,mul_pow,← div_div]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  exact (div_le_iff₀ (by positivity : (0 : ℝ)<(((2*n+1 : ℕ) : ℝ))^2)).mpr hb

lemma window_error_limit :
    Tendsto (fun n : ℕ ↦
      (∑ k∈squareWindow n, ((sumRep (roundedSet profile) k : ℝ)-(harmonic (k+1) : ℝ)))/
        (((2*n+1 : ℕ) : ℝ)*Real.log (n^2 : ℕ))) atTop (𝓝 0) := by
  have hinv := square_log_atTop.const_div_atTop 1
  have hbound : Tendsto (fun n : ℕ ↦ 400*(1+Real.log 9+Real.log (n^2 : ℕ))/
      (Real.log (n^2 : ℕ))^2) atTop (𝓝 0) := by
    have hh := (hinv.add ((hinv.pow 2).const_mul (1+Real.log 9))).const_mul 400
    simp only [zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 2] with n hn
    field_simp
    <;> ring
  have hsq : Tendsto (fun n : ℕ ↦
      ((∑ k∈squareWindow n, ((sumRep (roundedSet profile) k : ℝ)-(harmonic (k+1) : ℝ)))/
        (((2*n+1 : ℕ) : ℝ)*Real.log (n^2 : ℕ)))^2) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n ↦ sq_nonneg _)) _ hbound
    filter_upwards [eventually_ge_atTop 2] with n hn
    exact normalized_window_error_sq hn
  have habs := hsq.sqrt
  simp only [Real.sqrt_zero,Real.sqrt_sq_eq_abs] at habs
  exact (tendsto_zero_iff_abs_tendsto_zero _).mpr habs

lemma harmonic_window_bounds (n : ℕ) :
    (((2*n+1 : ℕ) : ℝ))*(harmonic (n^2+1) : ℝ) ≤
      ∑ k∈squareWindow n, (harmonic (k+1) : ℝ) ∧
    (∑ k∈squareWindow n, (harmonic (k+1) : ℝ)) ≤
      (((2*n+1 : ℕ) : ℝ))*(harmonic ((n+1)^2+1) : ℝ) := by
  have hlo : (∑ _k∈squareWindow n, (harmonic (n^2+1) : ℝ)) ≤
      ∑ k∈squareWindow n, (harmonic (k+1) : ℝ) := by
    apply Finset.sum_le_sum
    intro k hk
    have hk := (Finset.mem_Ico.mp hk).1
    exact harmonic_monotone_real (by omega)
  have hhi : (∑ k∈squareWindow n, (harmonic (k+1) : ℝ)) ≤
      ∑ _k∈squareWindow n, (harmonic ((n+1)^2+1) : ℝ) := by
    apply Finset.sum_le_sum
    intro k hk
    have hk := (Finset.mem_Ico.mp hk).2
    exact harmonic_monotone_real (by omega)
  simpa only [Finset.sum_const,nsmul_eq_mul,squareWindow_card] using And.intro hlo hhi

lemma upper_harmonic_square {n : ℕ} (hn : 1 ≤ n) :
    (harmonic ((n+1)^2+1) : ℝ) ≤ 1+Real.log 5+Real.log (n^2 : ℕ) := by
  have hh := harmonic_le_one_add_log ((n+1)^2+1)
  have hpow : (n+1)^2+1 ≤ 5*n^2 := by nlinarith
  have hlog := Real.log_le_log (by positivity : (0 : ℝ)<(((n+1)^2+1 : ℕ) : ℝ))
    (show ((((n+1)^2+1 : ℕ) : ℝ)) ≤ ((5*n^2 : ℕ) : ℝ) by exact_mod_cast hpow)
  have hn0 : ((n^2 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (pow_ne_zero 2 (show n ≠ 0 by omega))
  rw [Nat.cast_mul,Nat.cast_ofNat,Real.log_mul (by norm_num) hn0] at hlog
  linarith

lemma harmonic_window_limit :
    Tendsto (fun n : ℕ ↦ (∑ k∈squareWindow n, (harmonic (k+1) : ℝ))/
      (((2*n+1 : ℕ) : ℝ)*Real.log (n^2 : ℕ))) atTop (𝓝 1) := by
  have hlo : Tendsto (fun n : ℕ ↦ (harmonic (n^2+1) : ℝ)/Real.log (n^2 : ℕ)) atTop (𝓝 1) :=
    harmonic_shift_log_ratio.comp (tendsto_pow_atTop (by decide : 2 ≠ 0))
  have hhi := (square_log_atTop.const_div_atTop (1+Real.log 5)).const_add 1
  simp only [add_zero] at hhi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hW : (0 : ℝ)<((2*n+1 : ℕ) : ℝ) := by positivity
    have hlog := square_log_pos hn
    have hh := (harmonic_window_bounds n).1
    apply (div_le_div_iff₀ hlog (mul_pos hW hlog)).mpr
    nlinarith
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hW : (0 : ℝ)<((2*n+1 : ℕ) : ℝ) := by positivity
    have hlog := square_log_pos hn
    have hupper := upper_harmonic_square (show 1 ≤ n by omega)
    have hm := mul_le_mul_of_nonneg_left hupper hW.le
    have hh := (harmonic_window_bounds n).2.trans hm
    apply (div_le_iff₀ (mul_pos hW hlog)).mpr
    have he : (1+(1+Real.log 5)/Real.log (n^2 : ℕ))*
        (((2*n+1 : ℕ) : ℝ)*Real.log (n^2 : ℕ))=
          (((2*n+1 : ℕ) : ℝ))*(1+Real.log 5+Real.log (n^2 : ℕ)) := by
      field_simp
      <;> ring
    rw [he]
    exact hh

/-- The explicit floor-rounded set satisfies the quadratic-window averaged
analogue of the conjectured limit. This does not give the pointwise limit. -/
theorem rounded_quadratic_window_limit :
    Tendsto (fun n : ℕ ↦
      (∑ k∈squareWindow n, (sumRep (roundedSet profile) k : ℝ))/
        (((2*n+1 : ℕ) : ℝ)*Real.log (n^2 : ℕ))) atTop (𝓝 1) := by
  have hh := harmonic_window_limit.add window_error_limit
  simp only [add_zero] at hh
  apply hh.congr
  intro n
  rw [Finset.sum_sub_distrib]
  ring

end Erdos66QuadraticWindowLimit
