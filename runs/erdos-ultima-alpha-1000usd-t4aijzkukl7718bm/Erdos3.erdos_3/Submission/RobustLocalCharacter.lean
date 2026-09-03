import Submission.DoublingOverlapEnergy

/-! Robust local-character approximation with a relative-doubling Fourier
bound. Approximate multiplicativity is required only on nonempty overlaps;
its error is not divided by the ambient density of the window. -/
namespace Erdos3RobustLocalCharacter
open Finset Erdos3DoublingOverlapEnergy Erdos3LocalCharacterApproximation
  Erdos3ExactPhaseLinearObstruction Erdos3StableMaskedUniformity
  Erdos3FiniteUniformity Erdos3FiniteFourier Erdos3CorrelationSifting Erdos3CorrelationMoments
open scoped BigOperators Classical Pointwise ComplexConjugate
set_option maxHeartbeats 6000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma approximate_mask_translation (W : Finset G) (q : G → ℂ) (hq : ∀ x, ‖q x‖ = 1)
    (h : G) (c : ℂ) (hc : ‖c‖ = 1) {a : ℝ} (ha : 0 ≤ a)
    (herr : ∀ x ∈ W, x+h ∈ W → ‖q (x+h)-c*q x‖ ≤ a) (x : G) :
    ‖mask W q (x+h)-c*mask W q x‖ ≤
      |indicator W (x+h)-indicator W x|+a*indicator W x := by
  by_cases hx : x ∈ W <;> by_cases hy : x+h ∈ W
  · simpa only [mask,indicator,if_pos hx,if_pos hy,sub_self,abs_zero,zero_add,mul_one] using herr x hx hy
  · simp only [mask,indicator,if_pos hx,if_neg hy,zero_sub,norm_neg,norm_mul,hc,hq,
      one_mul,abs_neg,abs_one,mul_one]
    linarith
  · simp only [mask,indicator,if_neg hx,if_pos hy,mul_zero,sub_zero,hq,abs_one,add_zero,le_refl]
  · simp only [mask,indicator,if_neg hx,if_neg hy,mul_zero,sub_zero,norm_zero,abs_zero,add_zero,le_refl]

lemma approximate_overlap_derivative (W : Finset G) (q : G → ℂ) (hq : ∀ x, ‖q x‖ = 1)
    (h : G) (c : ℂ) {a : ℝ}
    (herr : ∀ x ∈ W, x+h ∈ W → ‖q (x+h)-c*q x‖ ≤ a) (x : G) :
    ‖derivative (mask W q) h x-c*((indicator W x*indicator W (x+h) : ℝ) : ℂ)‖ ≤
      a*(indicator W x*indicator W (x+h)) := by
  by_cases hx : x ∈ W <;> by_cases hy : x+h ∈ W
  · have he : q (x+h)*conj (q x)-c = (q (x+h)-c*q x)*conj (q x) := by
      rw [sub_mul,mul_assoc,mul_conj_eq_one (hq x),mul_one]
    simp only [derivative,mask,indicator,if_pos hx,if_pos hy,one_mul,Complex.ofReal_one,mul_one]
    rw [he,norm_mul,Complex.norm_conj,hq,mul_one]
    exact herr x hx hy
  · simp only [derivative,mask,indicator,if_pos hx,if_neg hy,zero_mul,mul_zero,Complex.ofReal_zero,sub_zero,norm_zero,le_refl]
  · simp only [derivative,mask,indicator,if_neg hx,if_pos hy,map_zero,zero_mul,mul_zero,Complex.ofReal_zero,sub_zero,norm_zero,le_refl]
  · simp only [derivative,mask,indicator,if_neg hx,if_neg hy,map_zero,zero_mul,mul_zero,Complex.ofReal_zero,sub_zero,norm_zero,le_refl]

lemma approximate_overlap_mean (W : Finset G) (q : G → ℂ) (hq : ∀ x, ‖q x‖ = 1)
    (h : G) (c : ℂ) {a : ℝ}
    (herr : ∀ x ∈ W, x+h ∈ W → ‖q (x+h)-c*q x‖ ≤ a) :
    ‖(𝔼 x : G, derivative (mask W q) h x)-c*(corr (indicator W) h : ℂ)‖ ≤
      a*corr (indicator W) h := by
  have he : (𝔼 x : G, c*((indicator W x*indicator W (x+h) : ℝ) : ℂ)) = c*(corr (indicator W) h : ℂ) := by
    rw [← mul_expect,← Complex.ofReal_expect]
    rfl
  rw [← he,← expect_sub_distrib]
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  have ht := expect_le_expect (s := univ) (fun x _ ↦ approximate_overlap_derivative W q hq h c herr x)
  rw [← mul_expect] at ht
  exact ht

lemma robust_local_U2_lower (W : Finset G) (q c : G → ℂ) (hq : ∀ x, ‖q x‖ = 1)
    (hc : ∀ h, ‖c h‖ = 1) {a : ℝ} (ha : a ≤ 1)
    (herr : ∀ h x, x ∈ W → x+h ∈ W → ‖q (x+h)-c h*q x‖ ≤ a) :
    (1-a)^2*(𝔼 h : G, (corr (indicator W) h)^2) ≤ uniformityPower 1 (mask W q) := by
  have hlow (h : G) : (1-a)*corr (indicator W) h ≤ ‖𝔼 x : G, derivative (mask W q) h x‖ := by
    have he := approximate_overlap_mean W q hq h (c h) (herr h)
    have hn := norm_sub_norm_le (c h*(corr (indicator W) h : ℂ)) (𝔼 x : G, derivative (mask W q) h x)
    rw [norm_mul,hc,one_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (corr_indicator_nonneg W h),norm_sub_rev] at hn
    nlinarith
  calc
    _ = 𝔼 h : G, ((1-a)*corr (indicator W) h)^2 := by simp only [mul_pow,← mul_expect]
    _ ≤ _ := expect_le_expect (fun h _ ↦ pow_le_pow_left₀
      (mul_nonneg (sub_nonneg.mpr ha) (corr_indicator_nonneg W h)) (hlow h) 2)

lemma robust_character_error (W : Finset G) (q : G → ℂ) (hq : ∀ x, ‖q x‖ = 1)
    (ψ : AddChar G ℂ) (h : G) (c : ℂ) (hc : ‖c‖ = 1) {a : ℝ} (ha : 0 ≤ a)
    (herr : ∀ x ∈ W, x+h ∈ W → ‖q (x+h)-c*q x‖ ≤ a) :
    ‖hat (mask W q) ψ‖*‖ψ h-c‖ ≤ boundary W h+a*density W := by
  have he : hat (fun x ↦ mask W q (x+h)-c*mask W q x) ψ = (ψ h-c)*hat (mask W q) ψ := by
    unfold hat
    simp only [sub_mul,mul_assoc,expect_sub_distrib,← mul_expect]
    change hat (fun x ↦ mask W q (x+h)) ψ-c*hat (mask W q) ψ =
      ψ h*hat (mask W q) ψ-c*hat (mask W q) ψ
    rw [hat_shift]
  calc
    _ = ‖hat (fun x ↦ mask W q (x+h)-c*mask W q x) ψ‖ := by rw [he,norm_mul,mul_comm]
    _ ≤ 𝔼 x : G, ‖mask W q (x+h)-c*mask W q x‖ := norm_hat_le _ _
    _ ≤ 𝔼 x : G, (|indicator W (x+h)-indicator W x|+a*indicator W x) :=
      expect_le_expect (fun x _ ↦ approximate_mask_translation W q hq h c hc ha herr x)
    _ = _ := by rw [expect_add_distrib,← mul_expect,expect_indicator]; rfl

/-- A normalized Fourier correlation >=rho is guaranteed as soon as
rho^2*K <=(1-a)^2, where K bounds relative difference doubling. The resulting
character approximates c(h) to (delta+a)/rho on any stable translation. -/
theorem exists_robust_local_character (W : Finset G) (hW : W.Nonempty)
    {K : ℝ} (hK : 0 < K) (hdoubling : ((W-W).card : ℝ) ≤ K*W.card)
    (q c : G → ℂ) (hq : ∀ x, ‖q x‖ = 1) (hc : ∀ h, ‖c h‖ = 1)
    {a ρ : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hρ : 0 < ρ) (hrho : ρ^2*K ≤ (1-a)^2)
    (herr : ∀ h x, x ∈ W → x+h ∈ W → ‖q (x+h)-c h*q x‖ ≤ a) :
    ∃ ψ : AddChar G ℂ, ρ ≤ ‖𝔼 x : W, q x*conj (ψ x)‖ ∧
      ∀ h : G, ∀ δ : ℝ,
        (𝔼 x : G, |normalized W (x+h)-normalized W x|) ≤ δ → ‖ψ h-c h‖ ≤ (δ+a)/ρ := by
  obtain ⟨ψ,hψ⟩ := exists_large_fourier_with_energy (mask W q)
  rw [mask_unit_energy W q hq] at hψ
  have hE := overlap_energy_doubling W hW hdoubling
  have hU := (robust_local_U2_lower W q c hq hc ha1 herr).trans hψ
  have hd := density_pos W hW
  have hmain : (1-a)^2*(density W)^2 ≤ K*‖hat (mask W q) ψ‖^2 := by
    have he := mul_le_mul_of_nonneg_left hE (sq_nonneg (1-a))
    have hu := mul_le_mul_of_nonneg_left hU hK.le
    nlinarith
  have hs : (ρ*density W)^2 ≤ ‖hat (mask W q) ψ‖^2 := by
    have hh := mul_le_mul_of_nonneg_right hrho (sq_nonneg (density W))
    nlinarith
  have hcoef : ρ*density W ≤ ‖hat (mask W q) ψ‖ := by
    nlinarith [norm_nonneg (hat (mask W q) ψ),mul_pos hρ hd]
  refine ⟨ψ,?_,?_⟩
  · rw [mask_hat_normalized W hW q ψ,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd] at hcoef
    nlinarith
  · intro h δ hδ
    have he := robust_character_error W q hq ψ h (c h) (hc h) ha (herr h)
    rw [boundary_normalized W hW h] at he
    have hh := mul_le_mul_of_nonneg_right hcoef (norm_nonneg (ψ h-c h))
    have hb := mul_le_mul_of_nonneg_left hδ hd.le
    apply (le_div_iff₀ hρ).mpr
    nlinarith

#print axioms exists_robust_local_character
end Erdos3RobustLocalCharacter
