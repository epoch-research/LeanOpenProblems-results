import Submission.QuadraticWindowLimitExplore

/-! A uniform moving-window averaged analogue for the canonical rounded
set. Window widths may vary between sqrt(n) and n. This is not a pointwise
representation theorem. -/
namespace Erdos66MovingWindowRounding
open AdditiveCombinatorics Erdos66Fractional Erdos66Rounding
  Erdos66CumulativeRoundingError Erdos66QuadraticWindowRounding
  Erdos66QuadraticWindowLimit Filter
open scoped Topology Classical
set_option maxHeartbeats 1500000

noncomputable def movingWindow (n w : ℕ) : Finset ℕ := Finset.Ico (n+1) (n+w+1)

lemma movingWindow_card (n w : ℕ) : (movingWindow n w).card=w := by
  simp only [movingWindow,Nat.card_Ico]
  omega

lemma movingWindow_sum (f : ℕ → ℝ) (n w : ℕ) :
    (∑ k∈movingWindow n w, f k)=prefixSum f (n+w)-prefixSum f n := by
  rw [movingWindow,Finset.sum_Ico_eq_sub f (by omega : n+1 ≤ n+w+1)]
  rfl

lemma rounded_moving_error (n w : ℕ) :
    |∑ k∈movingWindow n w, ((sumRep (roundedSet profile) k : ℝ)-(harmonic (k+1) : ℝ))| ≤
      4*Real.sqrt (prefixMajorant (n+w))+2 := by
  rw [movingWindow_sum]
  have h₁ := rounded_cumulative_error_bound (n+w)
  have h₂ := rounded_cumulative_error_bound n
  have hmono := Real.sqrt_le_sqrt (prefixMajorant_mono (show n ≤ n+w by omega))
  change |prefixSum (fun k ↦ (sumRep (roundedSet profile) k : ℝ)-(harmonic (k+1) : ℝ)) (n+w)| ≤
    2*Real.sqrt (prefixMajorant (n+w))+1 at h₁
  change |prefixSum (fun k ↦ (sumRep (roundedSet profile) k : ℝ)-(harmonic (k+1) : ℝ)) n| ≤
    2*Real.sqrt (prefixMajorant n)+1 at h₂
  have hh := abs_sub_le (prefixSum (fun k ↦ (sumRep (roundedSet profile) k : ℝ)-(harmonic (k+1) : ℝ)) (n+w))
    0 (prefixSum (fun k ↦ (sumRep (roundedSet profile) k : ℝ)-(harmonic (k+1) : ℝ)) n)
  simp only [sub_zero,zero_sub,abs_neg] at hh
  linarith

lemma prefixMajorant_double_bound {n w : ℕ} (hn : 1 ≤ n) (hw : w ≤ n) :
    prefixMajorant (n+w) ≤ 5*(n : ℝ)*(1+Real.log 5+Real.log n) := by
  have harg : 2*(n+w)+1 ≤ 5*n := by omega
  have hlog := Real.log_le_log (by positivity : (0 : ℝ)<((2*(n+w)+1 : ℕ) : ℝ))
    (show (((2*(n+w)+1 : ℕ) : ℝ)) ≤ ((5*n : ℕ) : ℝ) by exact_mod_cast harg)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [Nat.cast_mul,Nat.cast_ofNat,Real.log_mul (by norm_num) hn0] at hlog
  have hh : (harmonic (2*(n+w)+1) : ℝ) ≤ 1+Real.log 5+Real.log n := by
    linarith [harmonic_le_one_add_log (2*(n+w)+1)]
  have hc : (((2*(n+w)+1 : ℕ) : ℝ)) ≤ 5*(n : ℝ) := by exact_mod_cast harg
  exact mul_le_mul hc hh (harmonic_nonneg_real _) (by positivity)

lemma rounded_moving_error_sq {n w : ℕ} (hn : 1 ≤ n) (hw : w ≤ n) :
    (∑ k∈movingWindow n w, ((sumRep (roundedSet profile) k : ℝ)-(harmonic (k+1) : ℝ)))^2 ≤
      200*(n : ℝ)*(1+Real.log 5+Real.log n) := by
  let B := prefixMajorant (n+w)
  have hB : 0 ≤ B := prefixMajorant_nonneg _
  have he := rounded_moving_error n w
  have hsq := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 4*Real.sqrt B+2)).mpr he
  rw [sq_abs] at hsq
  have hsqrt := Real.sq_sqrt hB
  have hbound := prefixMajorant_double_bound hn hw
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  have hlogn := Real.log_natCast_nonneg n
  have hnon : 0 ≤ (n : ℝ)*(Real.log 5+Real.log n) := by positivity
  change B ≤ _ at hbound
  nlinarith [sq_nonneg (4*Real.sqrt B-2)]

lemma normalized_moving_error_sq {n w : ℕ} (hn : 2 ≤ n) (hw : w ≤ n) (hnw : n ≤ w^2) :
    ((∑ k∈movingWindow n w, ((sumRep (roundedSet profile) k : ℝ)-(harmonic (k+1) : ℝ)))/
      ((w : ℝ)*Real.log n))^2 ≤ 200*(1+Real.log 5+Real.log n)/(Real.log n)^2 := by
  have hwp : 0<w := by nlinarith
  have hW : (n : ℝ) ≤ (w : ℝ)^2 := by exact_mod_cast hnw
  have he := rounded_moving_error_sq (show 1 ≤ n by omega) hw
  have hL : 0 ≤ 1+Real.log 5+Real.log n := by
    have h5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
    have hn0 := Real.log_natCast_nonneg n
    linarith
  have hm := mul_le_mul_of_nonneg_left hW (by positivity : 0 ≤ 200*(1+Real.log 5+Real.log n))
  have hb : (∑ k∈movingWindow n w, ((sumRep (roundedSet profile) k : ℝ)-(harmonic (k+1) : ℝ)))^2 ≤
      (200*(1+Real.log 5+Real.log n))*(w : ℝ)^2 := by nlinarith
  rw [div_pow,mul_pow,← div_div]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  exact (div_le_iff₀ (by positivity : (0 : ℝ)<(w : ℝ)^2)).mpr hb

lemma moving_harmonic_bounds (n w : ℕ) :
    (w : ℝ)*(harmonic (n+1) : ℝ) ≤ ∑ k∈movingWindow n w, (harmonic (k+1) : ℝ) ∧
    (∑ k∈movingWindow n w, (harmonic (k+1) : ℝ)) ≤ (w : ℝ)*(harmonic (n+w+1) : ℝ) := by
  have hlo : (∑ _k∈movingWindow n w, (harmonic (n+1) : ℝ)) ≤
      ∑ k∈movingWindow n w, (harmonic (k+1) : ℝ) := by
    apply Finset.sum_le_sum
    intro k hk
    exact harmonic_monotone_real (by have := (Finset.mem_Ico.mp hk).1; omega)
  have hhi : (∑ k∈movingWindow n w, (harmonic (k+1) : ℝ)) ≤
      ∑ _k∈movingWindow n w, (harmonic (n+w+1) : ℝ) := by
    apply Finset.sum_le_sum
    intro k hk
    exact harmonic_monotone_real (by have := (Finset.mem_Ico.mp hk).2; omega)
  simpa only [Finset.sum_const,nsmul_eq_mul,movingWindow_card] using And.intro hlo hhi

lemma moving_harmonic_upper {n w : ℕ} (hn : 1 ≤ n) (hw : w ≤ n) :
    (harmonic (n+w+1) : ℝ) ≤ 1+Real.log 3+Real.log n := by
  have harg : n+w+1 ≤ 3*n := by omega
  have hlog := Real.log_le_log (by positivity : (0 : ℝ)<((n+w+1 : ℕ) : ℝ))
    (show (((n+w+1 : ℕ) : ℝ)) ≤ ((3*n : ℕ) : ℝ) by exact_mod_cast harg)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [Nat.cast_mul,Nat.cast_ofNat,Real.log_mul (by norm_num) hn0] at hlog
  linarith [harmonic_le_one_add_log (n+w+1)]

end Erdos66MovingWindowRounding
