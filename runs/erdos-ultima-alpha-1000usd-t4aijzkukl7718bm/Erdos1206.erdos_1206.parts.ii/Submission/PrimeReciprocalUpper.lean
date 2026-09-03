import Submission.QuadraticPrimePrefixBounds

/-! A logarithmic upper bound for finite prime reciprocal mass. -/
namespace Erdos1206.PrimeReciprocalUpper
open Finset Filter RealQuadraticEulerMass FinitePrimeMass QuadraticPrimeMassNearOne
open QuadraticPrimePrefixBounds
open scoped Topology Classical

lemma smoothed_mass_le_log_zeta {s : ℝ} (hs : 1 < s) :
    (∑' p : Nat.Primes, primePower s p) ≤ Real.log ‖riemannZeta (s:ℂ)‖ := by
  rw [real_log_zeta hs]
  have htriv := summable_real_log (1:DirichletCharacter ℤ 1)
    (fun n => Or.inr (Or.inl (by simp [MulChar.one_apply (isUnit_of_subsingleton _)]))) hs
  simp only [MulChar.one_apply (isUnit_of_subsingleton _),Int.cast_one,one_mul] at htriv
  apply Summable.tsum_le_tsum _ (summable_primePower hs) htriv
  intro p
  have hx := primePower_le_half hs p
  have hh := Real.log_le_sub_one_of_pos (show 0 < 1-primePower s p by linarith)
  linarith

lemma eventually_log_zeta_upper :
    ∀ᶠ s : ℝ in 𝓝[>] 1,
      Real.log ‖riemannZeta (s:ℂ)‖ ≤ Real.log (1/(s-1))+Real.log 2 := by
  have ht := (riemannZeta_residue_one.comp ofReal_tendsto_punctured_one).norm
  have hh : ∀ᶠ s : ℝ in 𝓝[>] 1, ‖((s:ℂ)-1)*riemannZeta (s:ℂ)‖ < (2:ℝ) := by
    simpa only [Function.comp_apply] using
      ht.eventually (by simpa only [norm_one] using
        (gt_mem_nhds (by norm_num : (1:ℝ) < 2)))
  filter_upwards [hh,self_mem_nhdsWithin] with s hs hs1
  have hsp : 0 < s-1 := sub_pos.mpr hs1
  have hn : ‖((s:ℂ)-1)*riemannZeta (s:ℂ)‖ = (s-1)*‖riemannZeta (s:ℂ)‖ := by
    rw [norm_mul,←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos hsp]
  rw [hn] at hs
  have hzpos : 0 < ‖riemannZeta (s:ℂ)‖ := by
    apply norm_pos_iff.mpr
    exact riemannZeta_ne_zero_of_one_lt_re hs1
  have hb : ‖riemannZeta (s:ℂ)‖ ≤ 2/(s-1) := by
    apply (le_div_iff₀ hsp).mpr
    nlinarith
  have hlog := Real.log_le_log hzpos hb
  rw [Real.log_div (by norm_num : (2:ℝ) ≠ 0) hsp.ne'] at hlog
  rw [Real.log_div (by norm_num : (1:ℝ) ≠ 0) hsp.ne',Real.log_one]
  linarith

lemma prefix_harmonic {s y : ℝ} (hs : 1 < s) (hy : 1 < y)
    (hscale : (s-1)*Real.log y ≤ 1) :
    (∑ p ∈ primePrefix y, 1/(p:ℝ)) ≤ Real.exp 1*Real.log ‖riemannZeta (s:ℂ)‖ := by
  calc
    _ ≤ ∑ p ∈ primePrefix y, Real.exp 1*primePower s p :=
      sum_le_sum (fun p hp => inverse_le_exp_primePower hs hy hscale p hp)
    _ = Real.exp 1*(∑ p ∈ primePrefix y, primePower s p) := by rw [mul_sum]
    _ ≤ Real.exp 1*(∑' p : Nat.Primes, primePower s p) := mul_le_mul_of_nonneg_left
      (Summable.sum_le_tsum _ (fun p _ => (primePower_pos s p).le) (summable_primePower hs))
      (Real.exp_pos _).le
    _ ≤ _ := mul_le_mul_of_nonneg_left (smoothed_mass_le_log_zeta hs) (Real.exp_pos _).le

theorem eventually_prefix_harmonic_upper :
    ∀ᶠ y : ℝ in atTop,
      (∑ p ∈ primePrefix y, 1/(p:ℝ)) ≤ Real.exp 1*(Real.log (Real.log y)+Real.log 2) := by
  filter_upwards [smoothing_tendsto.eventually eventually_log_zeta_upper,
    eventually_gt_atTop (1:ℝ)] with y hy hy1
  have hs : 1 < 1+1/Real.log y := by
    have := one_div_pos.mpr (Real.log_pos hy1)
    linarith
  have hscale : ((1+1/Real.log y)-1)*Real.log y=1 := by
    rw [add_sub_cancel_left]
    field_simp [(Real.log_pos hy1).ne']
  have hh := prefix_harmonic hs hy1 hscale.le
  have hm := mul_le_mul_of_nonneg_left hy (Real.exp_pos 1).le
  simp only [add_sub_cancel_left,one_div_one_div] at hm
  exact hh.trans hm

#print axioms smoothed_mass_le_log_zeta
#print axioms eventually_log_zeta_upper
#print axioms eventually_prefix_harmonic_upper
end Erdos1206.PrimeReciprocalUpper
