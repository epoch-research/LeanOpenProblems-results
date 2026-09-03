import Submission.AveragedLocalCircleCounting

/-! Positive finite Fourier kernels. A set S of dual characters gives a
probability kernel with Fourier support in S/S, whose coefficients measure
translated overlap of S. This separates frequency cutoff from ambient size. -/
namespace Erdos3PositiveSpectralKernel
open Finset Erdos3FiniteFourier Erdos3DissociatedRiesz
open scoped BigOperators Classical ComplexConjugate Pointwise
set_option maxHeartbeats 5000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def spectralKernel (S : Finset (AddChar G ℂ)) (x : G) : ℝ :=
  ‖∑ χ ∈ S, χ x‖^2/(S.card : ℝ)

lemma spectralKernel_nonneg (S : Finset (AddChar G ℂ)) (x : G) : 0 ≤ spectralKernel S x := by
  unfold spectralKernel
  positivity

lemma spectralKernel_mean (S : Finset (AddChar G ℂ)) (hS : S.Nonempty) :
    (𝔼 x : G, spectralKernel S x) = 1 := by
  have he := expect_norm_sq_sum_chars S id (fun _ ↦ (1 : ℂ)) Function.injective_id.injOn
  simp only [id_eq,one_mul,norm_one,one_pow,sum_const,nsmul_eq_mul,mul_one] at he
  unfold spectralKernel
  rw [← expect_div,he]
  exact div_self (by exact_mod_cast hS.card_pos.ne')

lemma spectralKernel_expansion (S : Finset (AddChar G ℂ)) (x : G) :
    (spectralKernel S x : ℂ) =
      (∑ b ∈ S, ∑ a ∈ S, (a/b) x)/(S.card : ℂ) := by
  unfold spectralKernel
  rw [Complex.ofReal_div]
  congr 1
  rw [← Complex.normSq_eq_norm_sq,← Complex.mul_conj,map_sum,mul_sum]
  apply sum_congr rfl
  intro b hb
  rw [sum_mul]
  apply sum_congr rfl
  intro a ha
  simp only [AddChar.div_apply,AddChar.map_neg_eq_inv,AddChar.inv_apply_eq_conj]

/-- Fourier coefficients are real nonnegative overlap ratios. -/
theorem spectralKernel_hat (S : Finset (AddChar G ℂ)) (ψ : AddChar G ℂ) :
    hat (fun x ↦ (spectralKernel S x : ℂ)) ψ =
      (((S.filter (fun b ↦ b*ψ ∈ S)).card : ℂ)/(S.card : ℂ)) := by
  unfold hat
  simp only [spectralKernel_expansion,div_mul_eq_mul_div,sum_mul,← expect_div,expect_sum_comm]
  congr 1
  have he (b a : AddChar G ℂ) :
      (𝔼 x : G, (a/b) x*conj (ψ x)) = if a = b*ψ then (1 : ℂ) else 0 := by
    rw [expect_char_mul_conj]
    have hh : a/b = ψ ↔ a = b*ψ := div_eq_iff_eq_mul'
    simp only [hh]
  simp only [he]
  have hs (b : AddChar G ℂ) : (∑ a ∈ S, if a = b*ψ then (1 : ℂ) else 0) =
      if b*ψ ∈ S then 1 else 0 := by simp
  simp only [hs]
  simp only [← sum_filter,sum_const,nsmul_eq_mul,mul_one]

lemma spectralKernel_hat_nonneg (S : Finset (AddChar G ℂ)) (ψ : AddChar G ℂ) :
    0 ≤ (hat (fun x ↦ (spectralKernel S x : ℂ)) ψ).re := by
  rw [spectralKernel_hat,← Complex.ofReal_natCast,← Complex.ofReal_natCast,← Complex.ofReal_div,
    Complex.ofReal_re]
  positivity

/-- The spectrum is supported on a difference set in the dual group. -/
theorem spectralKernel_hat_support (S : Finset (AddChar G ℂ)) (ψ : AddChar G ℂ)
    (hψ : ψ ∉ S/S) : hat (fun x ↦ (spectralKernel S x : ℂ)) ψ = 0 := by
  rw [spectralKernel_hat]
  have hempty : S.filter (fun b ↦ b*ψ ∈ S) = ∅ := by
    apply filter_eq_empty_iff.mpr
    intro b hb hab
    apply hψ
    exact mem_div.mpr ⟨b*ψ,hab,b,hb,mul_div_cancel_left b ψ⟩
  simp only [hempty,card_empty,Nat.cast_zero,zero_div]

lemma unit_chord_square (v : ℂ) (hv : ‖v‖ = 1) : ‖v-1‖^2 = 2*(1-v.re) := by
  rw [Complex.sq_norm,Complex.normSq_sub,Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_norm_sq,hv,norm_one,one_pow,map_one,mul_one]
  ring

/-- Kernel mass away from a coordinate's identity is exactly controlled by
the boundary of S in that dual-coordinate direction. -/
theorem spectralKernel_chord_moment (S : Finset (AddChar G ℂ)) (hS : S.Nonempty)
    (ψ : AddChar G ℂ) :
    (𝔼 x : G, spectralKernel S x*‖ψ x-1‖^2) =
      2*(1-((S.filter (fun b ↦ b*ψ ∈ S)).card : ℝ)/(S.card : ℝ)) := by
  have hh := congrArg Complex.re (spectralKernel_hat S ψ)
  have hr : (hat (fun x ↦ (spectralKernel S x : ℂ)) ψ).re =
      𝔼 x : G, spectralKernel S x*(ψ x).re := by
    unfold hat
    rw [Complex.re_expect]
    apply expect_congr rfl
    intro x _
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,Complex.conj_re]
  rw [hr] at hh
  simp only [← Complex.ofReal_natCast,← Complex.ofReal_div,Complex.ofReal_re] at hh
  simp only [unit_chord_square _ (ψ.norm_apply _)]
  have he (x : G) : spectralKernel S x*(2*(1-(ψ x).re)) =
      2*spectralKernel S x-2*(spectralKernel S x*(ψ x).re) := by ring
  simp only [he,expect_sub_distrib,← mul_expect,spectralKernel_mean S hS,hh]
  ring

#print axioms spectralKernel_hat
#print axioms spectralKernel_hat_support
#print axioms spectralKernel_chord_moment
end Erdos3PositiveSpectralKernel
