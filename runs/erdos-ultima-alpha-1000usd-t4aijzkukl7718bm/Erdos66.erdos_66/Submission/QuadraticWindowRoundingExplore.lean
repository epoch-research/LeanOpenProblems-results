import Submission.CumulativeRoundingErrorExplore

/-! The canonical floor rounding has logarithmically correct representation
averages between consecutive square cutoffs. The theorem is averaged, not
pointwise, and does not resolve Erdős 66. -/
namespace Erdos66QuadraticWindowRounding
open AdditiveCombinatorics Erdos66Fractional Erdos66Rounding Erdos66Generating
  Erdos66CumulativeRoundingError Filter
open scoped Topology Classical
set_option maxHeartbeats 1500000

noncomputable def squareWindow (n : ℕ) : Finset ℕ := Finset.Ico (n^2+1) ((n+1)^2+1)

lemma squareWindow_card (n : ℕ) : (squareWindow n).card=2*n+1 := by
  simp only [squareWindow,Nat.card_Ico]
  have he : (n+1)^2=n^2+2*n+1 := by ring
  omega

lemma squareWindow_sum (f : ℕ → ℝ) (n : ℕ) :
    (∑ k∈squareWindow n, f k)=prefixSum f ((n+1)^2)-prefixSum f (n^2) := by
  have he : (n+1)^2=n^2+2*n+1 := by ring
  rw [squareWindow,Finset.sum_Ico_eq_sub f (by omega : n^2+1 ≤ (n+1)^2+1)]
  rfl

lemma harmonic_nonneg_real (n : ℕ) : 0 ≤ (harmonic n : ℝ) := by
  have hh := harmonic_monotone_real (show 0 ≤ n by omega)
  simpa only [harmonic_zero,Rat.cast_zero] using hh

noncomputable def prefixMajorant (N : ℕ) : ℝ := ((2*N+1 : ℕ) : ℝ)*(harmonic (2*N+1) : ℝ)

lemma prefixMajorant_nonneg (N : ℕ) : 0 ≤ prefixMajorant N :=
  mul_nonneg (Nat.cast_nonneg _) (harmonic_nonneg_real _)

lemma prefixMajorant_mono : Monotone prefixMajorant := by
  intro N M hNM
  apply mul_le_mul
  · exact_mod_cast (show 2*N+1 ≤ 2*M+1 by omega)
  · exact harmonic_monotone_real (by omega)
  · exact harmonic_nonneg_real _
  · positivity

lemma rounded_window_error (n : ℕ) :
    |∑ k∈squareWindow n, ((sumRep (roundedSet profile) k : ℝ)-(harmonic (k+1) : ℝ))| ≤
      4*Real.sqrt (prefixMajorant ((n+1)^2))+2 := by
  rw [squareWindow_sum]
  have h₁ := rounded_cumulative_error_bound ((n+1)^2)
  have h₂ := rounded_cumulative_error_bound (n^2)
  have he : (n+1)^2=n^2+2*n+1 := by ring
  have hmono := Real.sqrt_le_sqrt (prefixMajorant_mono (show n^2 ≤ (n+1)^2 by omega))
  change |prefixSum (fun k ↦ (sumRep (roundedSet profile) k : ℝ)-(harmonic (k+1) : ℝ)) ((n+1)^2)| ≤
    2*Real.sqrt (prefixMajorant ((n+1)^2))+1 at h₁
  change |prefixSum (fun k ↦ (sumRep (roundedSet profile) k : ℝ)-(harmonic (k+1) : ℝ)) (n^2)| ≤
    2*Real.sqrt (prefixMajorant (n^2))+1 at h₂
  have hh := abs_sub_le (prefixSum (fun k ↦ (sumRep (roundedSet profile) k : ℝ)-(harmonic (k+1) : ℝ)) ((n+1)^2))
    0 (prefixSum (fun k ↦ (sumRep (roundedSet profile) k : ℝ)-(harmonic (k+1) : ℝ)) (n^2))
  simp only [sub_zero,zero_sub,abs_neg] at hh
  linarith

lemma prefixMajorant_square_bound {n : ℕ} (hn : 1 ≤ n) :
    prefixMajorant ((n+1)^2) ≤ 9*(n : ℝ)^2*(1+Real.log 9+Real.log (n^2 : ℕ)) := by
  have hpow : 2*(n+1)^2+1 ≤ 9*n^2 := by nlinarith
  have harg0 : (0 : ℝ)<((2*(n+1)^2+1 : ℕ) : ℝ) := by positivity
  have hlog := Real.log_le_log harg0 (show (((2*(n+1)^2+1 : ℕ) : ℝ)) ≤ (9*n^2 : ℕ) by exact_mod_cast hpow)
  have hhi : (harmonic (2*(n+1)^2+1) : ℝ) ≤ 1+Real.log (9*n^2 : ℕ) := by
    linarith [harmonic_le_one_add_log (2*(n+1)^2+1)]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [Nat.cast_mul,Nat.cast_ofNat,Real.log_mul (by norm_num) (by exact_mod_cast (pow_ne_zero 2 (show n ≠ 0 by omega)))] at hhi
  have hc : (((2*(n+1)^2+1 : ℕ) : ℝ)) ≤ 9*(n : ℝ)^2 := by exact_mod_cast hpow
  exact mul_le_mul hc (by simpa only [add_assoc] using hhi) (harmonic_nonneg_real _) (by positivity)

lemma rounded_window_error_sq {n : ℕ} (hn : 1 ≤ n) :
    (∑ k∈squareWindow n, ((sumRep (roundedSet profile) k : ℝ)-(harmonic (k+1) : ℝ)))^2 ≤
      400*(n : ℝ)^2*(1+Real.log 9+Real.log (n^2 : ℕ)) := by
  let B := prefixMajorant ((n+1)^2)
  have hB : 0 ≤ B := prefixMajorant_nonneg _
  have he := rounded_window_error n
  have hsq := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 4*Real.sqrt B+2)).mpr he
  rw [sq_abs] at hsq
  have hsqrt := Real.sq_sqrt hB
  have hbound := prefixMajorant_square_bound hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog9 : 0 ≤ Real.log 9 := Real.log_nonneg (by norm_num)
  have hlogn : 0 ≤ Real.log (n^2 : ℕ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n^2 by nlinarith))
  have hnon : 0 ≤ (n : ℝ)^2*(Real.log 9+Real.log (n^2 : ℕ)) := by positivity
  change B ≤ _ at hbound
  nlinarith [sq_nonneg (4*Real.sqrt B-2)]

end Erdos66QuadraticWindowRounding
