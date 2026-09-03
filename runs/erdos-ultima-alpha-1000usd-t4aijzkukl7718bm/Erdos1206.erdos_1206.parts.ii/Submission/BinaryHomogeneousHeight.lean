import FormalConjecturesUtil

/-!
Archimedean height and integral cancellation bounds for a fixed binary family.
Uniformity across all possible families is not asserted.
-/
namespace Erdos1206.BinaryHomogeneousHeight
open scoped BigOperators

/-- A continuous homogeneous map without a nonzero real zero has a uniform
positive lower height bound on its unit sphere. -/
theorem homogeneous_lower_bound {m d : ℕ} (hd : 0 < d)
    (F : (ℝ × ℝ) → (Fin m → ℝ)) (hcont : Continuous F)
    (hhom : ∀ (s : ℝ) x, F (s • x)=s^d • F x)
    (hzero : ∀ x, F x=0 → x=0) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, c*‖x‖^d ≤ ‖F x‖ := by
  have hne : (Metric.sphere (0:ℝ × ℝ) 1).Nonempty := by
    refine ⟨(1,0),?_⟩
    simp [Prod.norm_def]
  obtain ⟨u,hu,hmin⟩ := (isCompact_sphere (0:ℝ × ℝ) 1).exists_isMinOn hne
    (continuous_norm.comp hcont).continuousOn
  have hun : ‖u‖=1 := by simpa [Metric.mem_sphere] using hu
  have hFu : 0 < ‖F u‖ := by
    apply norm_pos_iff.mpr
    intro he
    have hz := hzero u he
    rw [hz,norm_zero] at hun
    norm_num at hun
  refine ⟨‖F u‖,hFu,fun x => ?_⟩
  by_cases hx : x=0
  · subst x
    simp only [norm_zero,zero_pow hd.ne',mul_zero]
    exact norm_nonneg _
  have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  let y := ‖x‖⁻¹ • x
  have hyn : ‖y‖=1 := by
    dsimp [y]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity),inv_mul_cancel₀ hxnorm]
  have hy : y ∈ Metric.sphere (0:ℝ × ℝ) 1 := by simpa [Metric.mem_sphere] using hyn
  have hmin' : ‖F u‖ ≤ ‖F y‖ := hmin hy
  have hxy : ‖x‖ • y=x := by
    dsimp [y]
    rw [smul_smul,mul_inv_cancel₀ hxnorm,one_smul]
  calc
    ‖F u‖*‖x‖^d ≤ ‖x‖^d*‖F y‖ := by
      nlinarith [mul_le_mul_of_nonneg_right hmin' (pow_nonneg (norm_nonneg x) d)]
    _ = ‖‖x‖^d • F y‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    _ = ‖F x‖ := by rw [← hhom,hxy]

/-- Homogeneous Bezout certificates bound every common divisor at a primitive
integer parameter. This is the step needed before canceling coordinates. -/
theorem common_divisor_dvd_certificate {ι : Type*} [Fintype ι]
    {u v g R : ℤ} {n : ℕ} {F H K : ι → ℤ}
    (hcop : IsCoprime u v) (hg : ∀ i, g ∣ F i)
    (hH : ∑ i, H i*F i=R*u^n) (hK : ∑ i, K i*F i=R*v^n) : g ∣ R := by
  have hgu : g ∣ R*u^n := by
    rw [← hH]
    exact Finset.dvd_sum (fun i _ => dvd_mul_of_dvd_right (hg i) _)
  have hgv : g ∣ R*v^n := by
    rw [← hK]
    exact Finset.dvd_sum (fun i _ => dvd_mul_of_dvd_right (hg i) _)
  have hcop' : IsCoprime (u^n) (v^n) := hcop.pow
  obtain ⟨a,b,hab⟩ := hcop'
  have hsum : R=a*(R*u^n)+b*(R*v^n) := by
    calc
      R = R*(a*u^n+b*v^n) := by rw [hab,mul_one]
      _ = _ := by ring
  rw [hsum]
  exact dvd_add (dvd_mul_of_dvd_right hgu _) (dvd_mul_of_dvd_right hgv _)

#print axioms homogeneous_lower_bound
#print axioms common_divisor_dvd_certificate
end Erdos1206.BinaryHomogeneousHeight
