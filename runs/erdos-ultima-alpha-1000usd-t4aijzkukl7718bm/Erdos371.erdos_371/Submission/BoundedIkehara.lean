import Submission.SummatoryLaplaceIdentity

/-! A bounded Wiener--Ikehara theorem for nonnegative Dirichlet coefficients.
The proof uses the checked positive-kernel Tauberian theorem and the explicit
summatory-function Fourier--Laplace identity. -/
namespace Erdos371.FourierBoundary
open Filter MeasureTheory FourierTransform Finset
open scoped Topology
set_option autoImplicit false

lemma fourier_sub_integrable (f g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g) (ξ : ℝ) :
    𝓕 (fun t => f t-g t) ξ = 𝓕 f ξ-𝓕 g ξ := by
  simp only [Real.fourier_real_eq,smul_sub]
  apply integral_sub
  · have hm := integrable_modulate hf (-ξ)
    change Integrable (fun t => 𝐞 (t*(-ξ)) • f t) at hm
    simpa only [mul_neg] using hm
  · have hm := integrable_modulate hg (-ξ)
    change Integrable (fun t => 𝐞 (t*(-ξ)) • g t) at hm
    simpa only [mul_neg] using hm

lemma fourier_const_mul (f : ℝ → ℂ) (c : ℂ) (ξ : ℝ) :
    𝓕 (fun t => c*f t) ξ = c*𝓕 f ξ := by
  simp only [Real.fourier_real_eq,Circle.smul_def,smul_eq_mul]
  simp_rw [mul_left_comm _ c]
  exact integral_const_mul _ _

lemma laplacePoint_ne_zero (σ ξ : ℝ) (hσ : 0 < σ) : laplacePoint σ ξ ≠ 0 := by
  intro he
  have hr := congrArg Complex.re he
  simp only [laplacePoint_re,Complex.zero_re] at hr
  linarith

lemma one_add_laplacePoint_ne_zero (σ ξ : ℝ) (hσ : 0 ≤ σ) : 1+laplacePoint σ ξ ≠ 0 := by
  intro he
  have hr := congrArg Complex.re he
  simp only [Complex.add_re,Complex.one_re,laplacePoint_re,Complex.zero_re] at hr
  linarith

lemma centeredExpSummatory_fourier (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ N : ℕ, (∑ n ∈ Icc 1 N, a n) ≤ C*N)
    (A σ ξ : ℝ) (hσ : 0 < σ) :
    𝓕 (damped (fun t => (centeredExpSummatory a A t : ℂ)) σ) ξ =
      LSeries (fun n => (a n : ℂ)) (1+laplacePoint σ ξ)/(1+laplacePoint σ ξ)-
        (A : ℂ)/(laplacePoint σ ξ) := by
  let b := fun t => (expSummatory a t : ℂ)
  let h := fun t => (halfLineUnit t : ℂ)
  have hbint : Integrable (damped b σ) := integrable_damped b
    (Complex.continuous_ofReal.comp_aestronglyMeasurable (expSummatory_measurable a).aestronglyMeasurable)
    C (fun t => by
      simpa only [b,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (expSummatory_nonneg a ha t)]
        using expSummatory_bound a C hC hbound t)
    (fun t ht => by simp only [b,expSummatory_zero_of_neg a t ht,Complex.ofReal_zero]) σ hσ
  have hhint : Integrable (damped h σ) := integrable_damped h
    (Complex.continuous_ofReal.comp_aestronglyMeasurable halfLineUnit_measurable.aestronglyMeasurable)
    1 (fun t => by dsimp [h,halfLineUnit]; split_ifs <;> norm_num)
    (fun t ht => by simp [h,halfLineUnit,not_le.mpr ht]) σ hσ
  have he : damped (fun t => (centeredExpSummatory a A t : ℂ)) σ =
      (fun t => damped b σ t-(A : ℂ)*damped h σ t) := by
    funext t
    simp only [damped,centeredExpSummatory,Complex.ofReal_sub,Complex.ofReal_mul,b,h]
    ring
  rw [he,fourier_sub_integrable _ _ hbint (hhint.const_mul (A : ℂ)),fourier_const_mul]
  have hs := one_add_laplacePoint_ne_zero σ ξ hσ.le
  have hL := LSeries_expSummatory_fourier a ha C hC hbound σ ξ hσ
  have hL' : 𝓕 (damped b σ) ξ = LSeries (fun n => (a n : ℂ)) (1+laplacePoint σ ξ)/(1+laplacePoint σ ξ) := by
    apply (eq_div_iff hs).mpr
    simpa only [mul_comm] using hL.symm
  rw [hL',fourier_damped_halfLineUnit σ ξ hσ]
  simp only [div_eq_mul_inv]

noncomputable def regularLaplaceBoundary (G : ℂ → ℂ) (A : ℝ) (p : ℝ × ℝ) : ℂ :=
  G (1+laplacePoint p.1 p.2)/(1+laplacePoint p.1 p.2)-(A : ℂ)/(1+laplacePoint p.1 p.2)

lemma regularLaplaceBoundary_continuous (G : ℂ → ℂ) (A : ℝ)
    (hG : ContinuousOn G {s : ℂ | 1 ≤ s.re}) :
    ContinuousOn (regularLaplaceBoundary G A) ((Set.Icc 0 1) ×ˢ Set.univ) := by
  have hz : Continuous (fun p : ℝ × ℝ => 1+laplacePoint p.1 p.2) := by
    unfold laplacePoint
    fun_prop
  have hmaps : Set.MapsTo (fun p : ℝ × ℝ => 1+laplacePoint p.1 p.2)
      ((Set.Icc 0 1) ×ˢ Set.univ) {s : ℂ | 1 ≤ s.re} := by
    intro p hp
    change 1 ≤ (1+laplacePoint p.1 p.2).re
    simp only [Complex.add_re,Complex.one_re,laplacePoint_re]
    linarith [hp.1.1]
  have hn (p : ℝ × ℝ) (hp : p ∈ ((Set.Icc 0 1) ×ˢ Set.univ)) : 1+laplacePoint p.1 p.2 ≠ 0 :=
    one_add_laplacePoint_ne_zero p.1 p.2 hp.1.1
  exact ((hG.comp hz.continuousOn hmaps).div hz.continuousOn hn).sub
    (continuousOn_const.div hz.continuousOn hn)

lemma centeredExpSummatory_regular_boundary (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ N : ℕ, (∑ n ∈ Icc 1 N, a n) ≤ C*N)
    (A : ℝ) (G : ℂ → ℂ)
    (hEq : ∀ s : ℂ, 1 < s.re → LSeries (fun n => (a n : ℂ)) s = G s+(A : ℂ)/(s-1))
    (σ ξ : ℝ) (hσ : 0 < σ) :
    𝓕 (damped (fun t => (centeredExpSummatory a A t : ℂ)) σ) ξ =
      regularLaplaceBoundary G A (σ,ξ) := by
  rw [centeredExpSummatory_fourier a ha C hC hbound A σ ξ hσ,
    hEq _ (by simp only [Complex.add_re,Complex.one_re,laplacePoint_re]; linarith)]
  have hz := laplacePoint_ne_zero σ ξ hσ
  have hs := one_add_laplacePoint_ne_zero σ ξ hσ.le
  simp only [regularLaplaceBoundary,add_sub_cancel_left]
  field_simp
  ring

/-- Nonnegative coefficients with a linear summatory bound satisfy the
Wiener--Ikehara conclusion when the pole-subtracted series has a continuous
extension to the entire boundary line. -/
theorem bounded_ikehara
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (C : ℝ) (hC : 0 < C) (hbound : ∀ N : ℕ, (∑ n ∈ Icc 1 N, a n) ≤ C*N)
    (A : ℝ) (G : ℂ → ℂ) (hG : ContinuousOn G {s : ℂ | 1 ≤ s.re})
    (hEq : ∀ s : ℂ, 1 < s.re → LSeries (fun n => (a n : ℂ)) s = G s+(A : ℂ)/(s-1)) :
    Tendsto (fun x : ℝ => summatory a x/x) atTop (𝓝 A) := by
  have hf := bounded_laplace_tauberian (centeredExpSummatory a A)
    (centeredExpSummatory_measurable a A).aestronglyMeasurable (C+|A|)
    (by linarith [abs_nonneg A]) (centeredExpSummatory_bound a ha C hC.le hbound A)
    (centeredExpSummatory_zero_of_neg a A)
    (centeredExpSummatory_slowlyDecreasing a ha C hC hbound A)
    (regularLaplaceBoundary G A) (regularLaplaceBoundary_continuous G A hG)
    (fun σ hσ _ ξ => centeredExpSummatory_regular_boundary a ha C hC.le hbound A G hEq σ ξ hσ)
  have ht := (hf.comp Real.tendsto_log_atTop).add_const A
  simp only [zero_add] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  simp only [Function.comp_apply,centeredExpSummatory,halfLineUnit,if_pos hlog,mul_one,sub_add_cancel,
    expSummatory,Real.exp_neg,Real.exp_log hx0,div_eq_mul_inv,mul_comm]

theorem bounded_ikehara_nat
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (C : ℝ) (hC : 0 < C) (hbound : ∀ N : ℕ, (∑ n ∈ Icc 1 N, a n) ≤ C*N)
    (A : ℝ) (G : ℂ → ℂ) (hG : ContinuousOn G {s : ℂ | 1 ≤ s.re})
    (hEq : ∀ s : ℂ, 1 < s.re → LSeries (fun n => (a n : ℂ)) s = G s+(A : ℂ)/(s-1)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, a n)/(N : ℝ)) atTop (𝓝 A) := by
  simpa only [Function.comp_def,summatory,Nat.floor_natCast] using
    (bounded_ikehara a ha C hC hbound A G hG hEq).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))

#print axioms bounded_ikehara_nat
end Erdos371.FourierBoundary
