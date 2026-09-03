import Submission.PositiveSpectralKernel

/-! Positive spectral smoothing preserves [0,1] bounds and means, has Fourier
support in a prescribed dual difference set, and approximates Lipschitz
observables when that dual set has small coordinate boundaries. -/
namespace Erdos3PositiveSpectralSmoothing
open Finset Erdos3PositiveSpectralKernel Erdos3FiniteFourier
  Erdos3FourierMultilinearTransfer Erdos3DerivativeSpectrum
open scoped BigOperators Classical ComplexConjugate Pointwise
set_option maxHeartbeats 6000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def spectralSmooth (S : Finset (AddChar G ℂ)) (f : G → ℝ) (x : G) : ℝ :=
  𝔼 y : G, spectralKernel S y*f (x-y)

lemma spectralSmooth_bounds (S : Finset (AddChar G ℂ)) (hS : S.Nonempty)
    (f : G → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (x : G) :
    0 ≤ spectralSmooth S f x ∧ spectralSmooth S f x ≤ 1 := by
  constructor
  · exact expect_nonneg (fun y _ ↦ mul_nonneg (spectralKernel_nonneg S y) (hf _).1)
  · calc
      _ ≤ 𝔼 y : G, spectralKernel S y*1 :=
        expect_le_expect (fun y _ ↦ mul_le_mul_of_nonneg_left (hf _).2 (spectralKernel_nonneg S y))
      _ = 1 := by simp only [mul_one,spectralKernel_mean S hS]

lemma spectralSmooth_mean (S : Finset (AddChar G ℂ)) (hS : S.Nonempty) (f : G → ℝ) :
    (𝔼 x : G, spectralSmooth S f x) = 𝔼 x : G, f x := by
  unfold spectralSmooth
  rw [expect_comm]
  have he (y : G) : (𝔼 x : G, f (x-y)) = 𝔼 x : G, f x :=
    Fintype.expect_equiv (Equiv.subRight y) _ _ (fun _ ↦ rfl)
  simp only [← mul_expect,he,← expect_mul,spectralKernel_mean S hS,one_mul]

lemma spectralSmooth_hat (S : Finset (AddChar G ℂ)) (f : G → ℝ) (ψ : AddChar G ℂ) :
    hat (fun x ↦ (spectralSmooth S f x : ℂ)) ψ =
      hat (fun x ↦ (spectralKernel S x : ℂ)) ψ*hat (fun x ↦ (f x : ℂ)) ψ := by
  unfold hat spectralSmooth
  simp only [Complex.ofReal_expect,Complex.ofReal_mul,expect_mul]
  rw [expect_comm]
  have he (y : G) : (𝔼 x : G, (spectralKernel S y : ℂ)*(f (x-y) : ℂ)*conj (ψ x)) =
      (spectralKernel S y : ℂ)*(conj (ψ y)*hat (fun x ↦ (f x : ℂ)) ψ) := by
    simp only [mul_assoc,← mul_expect]
    congr 1
    have h := hat_shift (fun x ↦ (f x : ℂ)) (-y) ψ
    simpa only [← sub_eq_add_neg,AddChar.map_neg_eq_inv,AddChar.inv_apply_eq_conj,hat] using h
  simp only [he,← mul_assoc,← expect_mul]
  rfl

lemma spectralSmooth_hat_support (S : Finset (AddChar G ℂ)) (f : G → ℝ)
    (ψ : AddChar G ℂ) (hψ : ψ ∉ S/S) : hat (fun x ↦ (spectralSmooth S f x : ℂ)) ψ = 0 := by
  rw [spectralSmooth_hat,spectralKernel_hat_support S ψ hψ,zero_mul]

lemma fourierMass_sq_le_support (f : G → ℂ) (T : Finset (AddChar G ℂ))
    (hs : ∀ χ, χ ∉ T → hat f χ = 0) :
    fourierMass f^2 ≤ (T.card : ℝ)*(𝔼 x : G, ‖f x‖^2) := by
  have he : fourierMass f = ∑ χ ∈ T, ‖hat f χ‖ := by
    symm
    apply sum_subset (subset_univ T)
    intro χ hχ hn
    rw [hs χ hn,norm_zero]
  rw [he]
  calc
    _ = (∑ χ ∈ T, 1*‖hat f χ‖)^2 := by simp only [one_mul]
    _ ≤ (∑ _χ ∈ T, (1 : ℝ)^2)*(∑ χ ∈ T, ‖hat f χ‖^2) := sum_mul_sq_le_sq_mul_sq ..
    _ ≤ (T.card : ℝ)*(∑ χ : AddChar G ℂ, ‖hat f χ‖^2) := by
      simp only [one_pow,sum_const,nsmul_eq_mul,mul_one]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact sum_le_sum_of_subset_of_nonneg (subset_univ T) (fun _ _ _ ↦ sq_nonneg _)
    _ = _ := by rw [parseval]

/-- This bound depends on the cutoff support, not the ambient group size. -/
theorem spectralSmooth_fourierMass_four (S : Finset (AddChar G ℂ)) (hS : S.Nonempty)
    (f : G → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    fourierMass (fun x ↦ (spectralSmooth S f x : ℂ))^4 ≤ ((S/S).card : ℝ)^2 := by
  have h := fourierMass_sq_le_support (fun x ↦ (spectralSmooth S f x : ℂ)) (S/S)
    (spectralSmooth_hat_support S f)
  have he : (𝔼 x : G, ‖(spectralSmooth S f x : ℂ)‖^2) ≤ 1 := by
    apply expect_le univ_nonempty
    intro x _
    rw [Complex.norm_real,Real.norm_eq_abs,sq_abs]
    exact pow_le_one₀ (spectralSmooth_bounds S hS f hf x).1 (spectralSmooth_bounds S hS f hf x).2
  have hsq := h.trans (by simpa only [mul_one] using
    mul_le_mul_of_nonneg_left he (Nat.cast_nonneg (S/S).card))
  simpa only [← pow_mul] using pow_le_pow_left₀ (sq_nonneg _) hsq 2

lemma probability_weighted_mean_le (w e : G → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hm : (𝔼 x : G, w x) = 1) {σ : ℝ} (hσ : 0 ≤ σ)
    (he : (𝔼 x : G, w x*(e x)^2) ≤ σ^2) : (𝔼 x : G, w x*e x) ≤ σ := by
  have hcs := expect_mul_sq_le_sq_mul_sq univ (fun x : G ↦ Real.sqrt (w x))
    (fun x : G ↦ Real.sqrt (w x)*e x)
  have hp (x : G) : Real.sqrt (w x)*(Real.sqrt (w x)*e x) = w x*e x := by
    rw [← mul_assoc,← pow_two,Real.sq_sqrt (hw x)]
  simp only [hp,mul_pow,Real.sq_sqrt (hw _),hm,one_mul] at hcs
  exact le_of_pow_le_pow_left₀ (by decide : (2 : ℕ) ≠ 0) hσ (hcs.trans he)

lemma character_translation_distance (ψ : AddChar G ℂ) (x y : G) :
    dist (ψ (x-y)) (ψ x) = ‖ψ y-1‖ := by
  rw [dist_eq_norm,char_sub]
  have he : ψ x*conj (ψ y)-ψ x = ψ x*conj (ψ y-1) := by
    rw [map_sub,map_one]
    ring
  rw [he,norm_mul,ψ.norm_apply,one_mul,Complex.norm_conj]

variable {I : Type*} [Fintype I]

/-- Small dual boundary yields uniform approximation of every Lipschitz
observable of the designated characters. Positivity is retained. -/
theorem spectralSmooth_approximation (S : Finset (AddChar G ℂ)) (hS : S.Nonempty)
    (ψ : I → AddChar G ℂ) (H : (I → ℂ) → ℝ) {L : NNReal} (hLip : LipschitzWith L H)
    (σ : I → ℝ) (hσ : ∀ i, 0 ≤ σ i)
    (hboundary : ∀ i, 2*(1-((S.filter (fun b ↦ b*ψ i ∈ S)).card : ℝ)/(S.card : ℝ)) ≤ (σ i)^2)
    (x : G) :
    |spectralSmooth S (fun y ↦ H (fun i ↦ ψ i y)) x-H (fun i ↦ ψ i x)| ≤
      (L : ℝ)*∑ i : I, σ i := by
  have he (y : G) : |H (fun i ↦ ψ i (x-y))-H (fun i ↦ ψ i x)| ≤
      (L : ℝ)*∑ i : I, ‖ψ i y-1‖ := by
    apply (hLip.dist_le_mul _ _).trans
    apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
    apply (dist_pi_le_iff (sum_nonneg (fun _ _ ↦ norm_nonneg _))).mpr
    intro i
    rw [character_translation_distance]
    exact single_le_sum (fun j _ ↦ norm_nonneg (ψ j y-1)) (mem_univ i)
  have hmoment (i : I) : (𝔼 y : G, spectralKernel S y*‖ψ i y-1‖) ≤ σ i :=
    probability_weighted_mean_le _ _ (spectralKernel_nonneg S) (spectralKernel_mean S hS)
      (hσ i) (by rw [spectralKernel_chord_moment S hS]; exact hboundary i)
  have hc : H (fun i ↦ ψ i x) = 𝔼 y : G, spectralKernel S y*H (fun i ↦ ψ i x) := by
    rw [← expect_mul,spectralKernel_mean S hS,one_mul]
  unfold spectralSmooth
  rw [hc,← expect_sub_distrib]
  calc
    _ ≤ 𝔼 y : G, |spectralKernel S y*(H (fun i ↦ ψ i (x-y))-H (fun i ↦ ψ i x))| := by
      simpa only [mul_sub] using Finset.abs_expect_le univ
        (fun y : G ↦ spectralKernel S y*H (fun i ↦ ψ i (x-y))-spectralKernel S y*H (fun i ↦ ψ i x))
    _ ≤ 𝔼 y : G, spectralKernel S y*((L : ℝ)*∑ i : I, ‖ψ i y-1‖) := by
      apply expect_le_expect
      intro y _
      rw [abs_mul,abs_of_nonneg (spectralKernel_nonneg S y)]
      exact mul_le_mul_of_nonneg_left (he y) (spectralKernel_nonneg S y)
    _ = (L : ℝ)*∑ i : I, 𝔼 y : G, spectralKernel S y*‖ψ i y-1‖ := by
      simp only [mul_left_comm (spectralKernel S _),← mul_expect,mul_sum,expect_sum_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_le_sum (fun i _ ↦ hmoment i)) L.coe_nonneg

#print axioms spectralSmooth_hat_support
#print axioms spectralSmooth_fourierMass_four
#print axioms spectralSmooth_approximation
end Erdos3PositiveSpectralSmoothing
