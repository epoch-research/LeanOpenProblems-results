import Submission.ScaledFractionalTailExplore

/-! Probability profiles with arbitrary positive logarithmic coefficient
and an explicit domination by a fixed multiple of the harmonic profile. -/
namespace Erdos66DominatedScaledProfile
open Erdos66ScaledFractionalTail Erdos66Fractional Erdos66FractionalFourthPower
open Filter AdditiveCombinatorics
open scoped Topology Classical
set_option maxHeartbeats 1500000

lemma exists_dominated_scaled_profile (c : ℝ) (hc : 0<c) :
    ∃ p : ℕ → ℝ, (∀ n, 0 ≤ p n ∧ p n ≤ 1) ∧
      (∀ n, p n ≤ Real.sqrt c*profile n) ∧
      Tendsto (fun n ↦ sumConv p p n/Real.log n) atTop (𝓝 c) := by
  let s := Real.sqrt c
  have hs : 0<s := Real.sqrt_pos.mpr hc
  have hlim := summable_profile_fourth.tendsto_atTop_zero.mul_const (s^4)
  simp only [zero_mul] at hlim
  obtain ⟨S,hS⟩ := (hlim.eventually_lt_const (by norm_num : (0:ℝ)<1)).exists
  have hscale : s*profile S ≤ 1 := by
    by_contra hh
    have hh' : 1<s*profile S := lt_of_not_ge hh
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) hh'.le 4
    have he : (s*profile S)^4=profile S^4*s^4 := by ring
    rw [he] at hp
    norm_num at hp
    linarith
  let p : ℕ → ℝ := fun n ↦ s*profile (n+S)
  have hp (n : ℕ) : 0 ≤ p n ∧ p n ≤ 1 := by
    refine ⟨mul_nonneg hs.le (profile_nonneg _),?_⟩
    exact (mul_le_mul_of_nonneg_left (profile_antitone (by omega : S≤n+S)) hs.le).trans hscale
  have he (n : ℕ) : sumConv p p n=c*tailConv S n := by
    dsimp only [sumConv,tailConv,p]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hs2 : s*s=c := Real.mul_self_sqrt hc.le
    rw [← hs2]
    ring
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hu := harmonic_shift_log_ratio.const_mul c
  simp only [mul_one] at hu
  have hl := hu.sub (hlog.const_div_atTop (2*S*c))
  simp only [sub_zero] at hl
  have hdom (n : ℕ) : p n ≤ Real.sqrt c*profile n := by
    exact mul_le_mul_of_nonneg_left (profile_antitone (Nat.le_add_right n S)) hs.le
  refine ⟨p,hp,hdom,tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu ?_ ?_⟩
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hln : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (show 1<n by omega))
    have hh := mul_le_mul_of_nonneg_left (tailConv_bounds S n).1 hc.le
    rw [he,←mul_div_assoc,←sub_div]
    apply div_le_div_of_nonneg_right _ hln.le
    nlinarith
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hln : 0≤Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤n by omega))
    rw [he,←mul_div_assoc]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (tailConv_bounds S n).2 hc.le) hln

end Erdos66DominatedScaledProfile
