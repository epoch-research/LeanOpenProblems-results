import Submission.RealQuadraticEulerMass

/-! Lower bounds for smoothed quadratic-prime mass near s=1. -/
namespace Erdos1206.QuadraticPrimeMassNearOne
open RealQuadraticEulerMass Filter
open scoped Topology

lemma ofReal_tendsto_punctured_one :
    Tendsto (fun s : ℝ => (s:ℂ)) (𝓝[>] 1) (𝓝[≠] 1) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [Complex.ofReal_one] using
      (Complex.continuous_ofReal.tendsto (1:ℝ)).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs
    change (s:ℂ) ∉ ({1}:Set ℂ)
    simp only [Set.mem_singleton_iff,←Complex.ofReal_one,Complex.ofReal_inj]
    exact (show 1 < s from hs).ne'

lemma eventually_log_zeta_lower :
    ∀ᶠ s : ℝ in 𝓝[>] 1,
      Real.log (1/(s-1))-Real.log 2 ≤ Real.log ‖riemannZeta (s:ℂ)‖ := by
  have ht := (riemannZeta_residue_one.comp ofReal_tendsto_punctured_one).norm
  have hh : ∀ᶠ s : ℝ in 𝓝[>] 1, (1/2:ℝ) < ‖((s:ℂ)-1)*riemannZeta (s:ℂ)‖ := by
    apply ht.eventually
    simpa only [norm_one] using (lt_mem_nhds (by norm_num : (1/2:ℝ) < 1))
  filter_upwards [hh,self_mem_nhdsWithin] with s hs hs1
  have hsp : 0 < s-1 := sub_pos.mpr hs1
  have hn : ‖((s:ℂ)-1)*riemannZeta (s:ℂ)‖ = (s-1)*‖riemannZeta (s:ℂ)‖ := by
    rw [norm_mul,←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos hsp]
  rw [hn] at hs
  have hb : 1/(2*(s-1)) ≤ ‖riemannZeta (s:ℂ)‖ := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hsp)).mpr
    nlinarith
  have hlog := Real.log_le_log (by positivity : 0 < (1:ℝ)/(2*(s-1))) hb
  rw [Real.log_div (by norm_num : (1:ℝ) ≠ 0) (mul_ne_zero (by norm_num) hsp.ne'),
    Real.log_one,Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hsp.ne'] at hlog
  rw [Real.log_div (by norm_num : (1:ℝ) ≠ 0) hsp.ne',Real.log_one]
  linarith

lemma eventually_log_LSeries_upper {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℤ N) (hnc : complexChar χ ≠ 1) :
    ∃ B : ℝ, ∀ᶠ s : ℝ in 𝓝[>] 1,
      Real.log ‖LSeries (fun n => complexChar χ (n:ZMod N)) (s:ℂ)‖ ≤ B := by
  let L := DirichletCharacter.LFunction (complexChar χ)
  let B : ℝ := ‖L 1‖+1
  have hc : ContinuousAt (fun s : ℝ => ‖L (s:ℂ)‖) 1 := by
    have hh := ((complexChar χ).differentiableAt_LFunction 1 (Or.inr hnc)).continuousAt
    exact hh.norm.comp_of_eq (Complex.continuous_ofReal.continuousAt (x := (1:ℝ)))
      (by simp)
  have hb : ∀ᶠ s : ℝ in 𝓝[>] 1, ‖L (s:ℂ)‖ < B :=
    (hc.eventually (gt_mem_nhds (lt_add_one _))).filter_mono nhdsWithin_le_nhds
  refine ⟨B,?_⟩
  filter_upwards [hb,self_mem_nhdsWithin] with s hs hs1
  have hsC : 1 < (s:ℂ).re := hs1
  have he : L (s:ℂ)=LSeries (fun n => complexChar χ (n:ZMod N)) (s:ℂ) :=
    (complexChar χ).LFunction_eq_LSeries hsC
  have hn : 0 < ‖L (s:ℂ)‖ := by
    rw [he]
    exact norm_pos_iff.mpr ((complexChar χ).LSeries_ne_zero_of_one_lt_re hsC)
  rw [←he]
  exact (Real.log_le_sub_one_of_pos hn).trans (by linarith)

/-- Only boundedness of the nonprincipal L-function is used for this lower
bound; a prime number theorem is not required. -/
theorem eventually_weightedMass_lower {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℤ N) (hnc : complexChar χ ≠ 1)
    (hχ : ∀ n : ℕ, χ (n:ZMod N)=0 ∨ χ (n:ZMod N)=1 ∨ χ (n:ZMod N) = -1) :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] 1,
      Real.log (1/(s-1))-C ≤ weightedMass χ s := by
  obtain ⟨B,hB⟩ := eventually_log_LSeries_upper χ hnc
  refine ⟨Real.log 2+B+squareError,?_⟩
  filter_upwards [eventually_log_zeta_lower,hB,self_mem_nhdsWithin] with s hz hL hs
  have hh := log_ratio_le_weightedMass χ hχ hs
  linarith

#print axioms eventually_log_zeta_lower
#print axioms eventually_log_LSeries_upper
#print axioms eventually_weightedMass_lower
end Erdos1206.QuadraticPrimeMassNearOne
