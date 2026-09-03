import Submission.NaturalScaleRankWindowExplore
import Submission.ProfileLowerGapExplore

/-! A logarithmically sharp lower bound for the harmonic fractional profile,
obtained from its convolution identity and monotonicity. -/
namespace Erdos66LogProfileLower
open AdditiveCombinatorics Erdos66Fractional Erdos66Generating Erdos66Rounding
  Erdos66CumulativeRoundingError Erdos66FlatProfileWindows
open scoped Classical
set_option maxHeartbeats 2200000

lemma antitone_half_convolution (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) (hanti : Antitone f) (n : ℕ) :
    sumConv f f (2*n) ≤ 2*f n*prefixSum f n := by
  have hleft : (∑ ab∈Finset.antidiagonal (2*n), if ab.1 ≤ n then f ab.1 else 0)=prefixSum f n := by
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,←Finset.sum_filter]
    have he : (Finset.range (2*n+1)).filter (fun i ↦ i ≤ n)=Finset.range (n+1) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_range]
      omega
    rw [he]
    rfl
  have hright : (∑ ab∈Finset.antidiagonal (2*n), if ab.2 ≤ n then f ab.2 else 0)=prefixSum f n := by
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    have hh := Finset.sum_range_reflect (fun i ↦ if i ≤ n then f i else 0) (2*n+1)
    simpa only [Nat.add_sub_cancel] using hh.trans (by
      simpa only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] using hleft)
  calc
    _ ≤ ∑ ab∈Finset.antidiagonal (2*n), f n*((if ab.1 ≤ n then f ab.1 else 0)+
        (if ab.2 ≤ n then f ab.2 else 0)) := by
      apply Finset.sum_le_sum
      intro ab hab
      have he := Finset.mem_antidiagonal.mp hab
      by_cases ha : ab.1 ≤ n
      · have hnb : n ≤ ab.2 := by omega
        have hh := mul_le_mul_of_nonneg_left (hanti hnb) (hf ab.1)
        rw [if_pos ha]
        split_ifs <;> nlinarith [hf ab.2,hf n]
      · have hb : ab.2 ≤ n := by omega
        have hh := mul_le_mul_of_nonneg_right (hanti (show n ≤ ab.1 by omega)) (hf ab.2)
        rw [if_neg ha,if_pos hb]
        simpa only [zero_add] using hh
    _ = _ := by rw [←Finset.mul_sum,Finset.sum_add_distrib,hleft,hright]; ring

lemma profile_log_square_lower (n : ℕ) :
    Real.log ((n : ℝ)+1) ≤ 4*((2*n+1 : ℕ) : ℝ)*(profile n)^2 := by
  have hhalf := antitone_half_convolution profile profile_nonneg profile_antitone n
  rw [profile_convolution] at hhalf
  have hHpos : (0 : ℝ)<(harmonic (2*n+1) : ℝ) := by
    have hh := harmonic_monotone_real (show 1 ≤ 2*n+1 by omega)
    dsimp only at hh
    rw [show (harmonic 1 : ℝ)=1 by norm_num] at hh
    linarith
  have hs := (sq_le_sq₀ hHpos.le (mul_nonneg (mul_nonneg (by norm_num) (profile_nonneg n)) (prefix_nonneg n))).mpr hhalf
  have hp := profile_prefix_square_bound n
  have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ 4*(profile n)^2 by positivity)
  have hcancel : (harmonic (2*n+1) : ℝ) ≤ 4*((2*n+1 : ℕ) : ℝ)*(profile n)^2 := by
    apply le_of_mul_le_mul_right (a := (harmonic (2*n+1) : ℝ)) _ hHpos
    nlinarith only [hs,hh]
  have hlog := log_add_one_le_harmonic (2*n+1)
  have hmono := Real.log_le_log (by positivity : (0 : ℝ)<(n : ℝ)+1)
    (show (n : ℝ)+1 ≤ ((2*n+1+1 : ℕ) : ℝ) by push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) n])
  exact (hmono.trans hlog).trans hcancel

end Erdos66LogProfileLower
