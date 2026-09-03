import Submission.DerivativeSpectrum
import Submission.LinearFormsUniformity

/-! A quantitative coherence estimate for derivative frequencies. Large correlation
with a family of modulated shifts forces additive energy in its frequency graph. -/
namespace Erdos3SpectralGraphEnergy
open Finset Erdos3DerivativeSpectrum Erdos3FiniteUniformity Erdos3FiniteFourier
  Erdos3LinearFormsUniformity Erdos3DissociatedRiesz
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 3000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma expect_pair {I J V : Type*} [Fintype I] [Fintype J] [AddCommMonoid V] [Module ℚ≥0 V]
    (f : I × J → V) : (𝔼 p, f p) = 𝔼 i, 𝔼 j, f (i,j) := expect_product _ _ _

lemma ofReal_expect {I : Type*} [Fintype I] (f : I → ℝ) :
    ((𝔼 i, f i : ℝ) : ℂ) = 𝔼 i, (f i : ℂ) :=
  map_expect ((algebraMap ℝ ℂ).toRatAlgHom.toLinearMap.restrictScalars ℚ≥0) _ univ

lemma ofReal_norm_expect_sq {I : Type*} [Fintype I] (f : I → ℂ) :
    ((‖𝔼 i, f i‖^2 : ℝ) : ℂ) = 𝔼 i, 𝔼 j, f i*conj (f j) := by
  rw [← Fintype.expect_mul_expect,← expect_conj,Complex.mul_conj,Complex.normSq_eq_norm_sq]

lemma norm_expect_sq_re {I : Type*} [Fintype I] (f : I → ℂ) :
    ‖𝔼 i, f i‖^2 = 𝔼 i, 𝔼 j, (f i*conj (f j)).re := by
  simpa only [Complex.ofReal_re,expect_re] using congrArg Complex.re (ofReal_norm_expect_sq f)

/-- Two Cauchy--Schwarz steps, written in kernel form. -/
lemma kernel_fourth_bound (K : G → G → ℂ) (f g : G → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ x, ‖g x‖ ≤ 1) :
    ‖𝔼 x, 𝔼 y, f x*K x y*g y‖^4 ≤
      𝔼 y, 𝔼 z, ‖𝔼 x, K x y*conj (K x z)‖^2 := by
  let R : ℝ := 𝔼 x, ‖𝔼 y, K x y*g y‖^2
  let B : G × G → ℂ := fun p ↦ g p.1*conj (g p.2)
  let L : G × G → ℂ := fun p ↦ 𝔼 x, K x p.1*conj (K x p.2)
  have hR : 0 ≤ R := expect_nonneg (fun _ _ ↦ sq_nonneg _)
  have hfirst : ‖𝔼 x, 𝔼 y, f x*K x y*g y‖^2 ≤ R := by
    have he : (𝔼 x, 𝔼 y, f x*K x y*g y) = 𝔼 x, f x*(𝔼 y, K x y*g y) := by
      simp_rw [mul_assoc,← mul_expect]
    rw [he]
    exact mean_product_sq_le f _ hf
  have hident : (R : ℂ) = 𝔼 p : G × G, B p*L p := by
    dsimp [R,B,L]
    rw [ofReal_expect]
    simp_rw [ofReal_norm_expect_sq,map_mul]
    rw [expect_pair]
    calc
      _ = 𝔼 y : G, 𝔼 x : G, 𝔼 z : G,
          K x y*g y*(conj (K x z)*conj (g z)) := expect_comm _ _ _
      _ = 𝔼 y : G, 𝔼 z : G, 𝔼 x : G,
          K x y*g y*(conj (K x z)*conj (g z)) := by
        apply expect_congr rfl
        intro y _
        exact expect_comm _ _ _
      _ = _ := by
        apply expect_congr rfl
        intro y _
        apply expect_congr rfl
        intro z _
        rw [mul_expect]
        apply expect_congr rfl
        intro x _
        ring
  have hB (p : G × G) : ‖B p‖ ≤ 1 := by
    dsimp [B]
    rw [norm_mul,Complex.norm_conj]
    exact (mul_le_mul (hg _) (hg _) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hsecond := mean_product_sq_le B L hB
  rw [← hident,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hR] at hsecond
  have hsecond' : R^2 ≤ 𝔼 y : G, 𝔼 z : G, ‖𝔼 x : G, K x y*conj (K x z)‖^2 := by
    exact hsecond.trans_eq (expect_product _ _ _)
  nlinarith [sq_nonneg (‖𝔼 x, 𝔼 y, f x*K x y*g y‖^2-R)]

/-- Normalized additive energy of a partial frequency graph. The parameters
(h,k,t) describe the parallelogram h,k,h-t,k-t. -/
noncomputable def graphEnergy (H : Finset G) (ξ : G → AddChar G ℂ) : ℝ :=
  𝔼 h, 𝔼 k, 𝔼 t,
    if h ∈ H ∧ k ∈ H ∧ h-t ∈ H ∧ k-t ∈ H ∧
      ξ h*ξ (k-t) = ξ k*ξ (h-t) then 1 else 0

noncomputable def shiftKernel (b : G → ℂ) (ξ : G → AddChar G ℂ) (x y : G) : ℂ :=
  b (y-x)*conj (ξ (y-x) x)

lemma shifted_quadruple (b : G → ℂ) (ξ : G → AddChar G ℂ) (x h k t : G) :
    shiftKernel b ξ x (x+h)*conj (shiftKernel b ξ x (x+k))*
      conj (shiftKernel b ξ (x+t) (x+h))*shiftKernel b ξ (x+t) (x+k) =
    (b h*conj (b k)*conj (b (h-t))*b (k-t)*ξ (h-t) t*conj (ξ (k-t) t))*
      ((ξ k*ξ (h-t)) x*conj ((ξ h*ξ (k-t)) x)) := by
  simp only [shiftKernel,add_sub_cancel_left,add_sub_add_left_eq_sub,map_mul,
    starRingEnd_self_apply,AddChar.map_add_eq_mul,AddChar.mul_apply]
  ring

lemma shifted_quadruple_expect (b : G → ℂ) (ξ : G → AddChar G ℂ) (h k t : G) :
    (𝔼 x, shiftKernel b ξ x (x+h)*conj (shiftKernel b ξ x (x+k))*
      conj (shiftKernel b ξ (x+t) (x+h))*shiftKernel b ξ (x+t) (x+k)) =
    (b h*conj (b k)*conj (b (h-t))*b (k-t)*ξ (h-t) t*conj (ξ (k-t) t))*
      (if ξ h*ξ (k-t) = ξ k*ξ (h-t) then 1 else 0) := by
  simp_rw [shifted_quadruple]
  rw [← mul_expect,expect_char_mul_conj]
  simp only [eq_comm]

lemma expect_rotate_three {I J K V : Type*} [Fintype I] [Fintype J] [Fintype K]
    [AddCommMonoid V] [Module ℚ≥0 V] (q : I → J → K → V) :
    (𝔼 i, 𝔼 j, 𝔼 k, q i j k) = 𝔼 k, 𝔼 i, 𝔼 j, q i j k := by
  calc
    _ = 𝔼 i, 𝔼 k, 𝔼 j, q i j k := by
      apply expect_congr rfl
      intro i _
      exact expect_comm _ _ _
    _ = _ := expect_comm _ _ _

lemma expect_shift_quad {V : Type*} [AddCommMonoid V] [Module ℚ≥0 V]
    (q : G → G → G → G → V) :
    (𝔼 y, 𝔼 z, 𝔼 x, 𝔼 w, q x y z w) =
      𝔼 h, 𝔼 k, 𝔼 t, 𝔼 x, q x (x+h) (x+k) (x+t) := by
  calc
    _ = 𝔼 x, 𝔼 y, 𝔼 z, 𝔼 w, q x y z w := expect_rotate_three _
    _ = 𝔼 x, 𝔼 h, 𝔼 k, 𝔼 t, q x (x+h) (x+k) (x+t) := by
      apply expect_congr rfl
      intro x _
      calc
        _ = 𝔼 h, 𝔼 z, 𝔼 w, q x (x+h) z w :=
          (Fintype.expect_equiv (Equiv.addLeft x) _ _ (fun _ ↦ rfl)).symm
        _ = _ := by
          apply expect_congr rfl
          intro h _
          calc
            _ = 𝔼 k, 𝔼 w, q x (x+h) (x+k) w :=
              (Fintype.expect_equiv (Equiv.addLeft x) _ _ (fun _ ↦ rfl)).symm
            _ = _ := by
              apply expect_congr rfl
              intro k _
              exact (Fintype.expect_equiv (Equiv.addLeft x) _ _ (fun _ ↦ rfl)).symm
    _ = 𝔼 h, 𝔼 k, 𝔼 x, 𝔼 t, q x (x+h) (x+k) (x+t) :=
      (expect_rotate_three _).symm
    _ = _ := by
      apply expect_congr rfl
      intro h _
      apply expect_congr rfl
      intro k _
      exact expect_comm _ _ _

lemma kernel_gram_shift (K : G → G → ℂ) :
    (𝔼 y, 𝔼 z, ‖𝔼 x, K x y*conj (K x z)‖^2) =
      𝔼 h, 𝔼 k, 𝔼 t,
        (𝔼 x, K x (x+h)*conj (K x (x+k))*conj (K (x+t) (x+h))*K (x+t) (x+k)).re := by
  simp_rw [norm_expect_sq_re,map_mul,starRingEnd_self_apply]
  have he (x y z w : G) :
      K x y*conj (K x z)*(conj (K w y)*K w z) =
      K x y*conj (K x z)*conj (K w y)*K w z := by ring
  simp_rw [he,expect_re]
  exact expect_shift_quad _

lemma shifted_quadruple_re_le (H : Finset G) (b : G → ℂ) (ξ : G → AddChar G ℂ)
    (hb : ∀ h, ‖b h‖ ≤ 1) (hsupp : ∀ h, h ∉ H → b h = 0) (h k t : G) :
    (𝔼 x, shiftKernel b ξ x (x+h)*conj (shiftKernel b ξ x (x+k))*
      conj (shiftKernel b ξ (x+t) (x+h))*shiftKernel b ξ (x+t) (x+k)).re ≤
    if h ∈ H ∧ k ∈ H ∧ h-t ∈ H ∧ k-t ∈ H ∧ ξ h*ξ (k-t) = ξ k*ξ (h-t)
      then 1 else 0 := by
  rw [shifted_quadruple_expect]
  by_cases hh : h ∈ H
  · by_cases hk : k ∈ H
    · by_cases hht : h-t ∈ H
      · by_cases hkt : k-t ∈ H
        · by_cases heq : ξ h*ξ (k-t) = ξ k*ξ (h-t)
          · simp only [hh,hk,hht,hkt,heq,and_self,if_true,mul_one]
            apply (Complex.re_le_norm _).trans
            simp only [norm_mul,Complex.norm_conj,AddChar.norm_apply,mul_one]
            have hp : ‖b h‖*‖b k‖ ≤ 1 :=
              (mul_le_mul (hb _) (hb _) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
            have hq : ‖b (h-t)‖*‖b (k-t)‖ ≤ 1 :=
              (mul_le_mul (hb _) (hb _) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
            nlinarith [mul_le_mul hp hq (by positivity) (by norm_num)]
          · simp [heq]
        · simp [hkt,hsupp _ hkt]
      · simp [hht,hsupp _ hht]
    · simp [hk,hsupp _ hk]
  · simp [hh,hsupp _ hh]

/-- Correlation with modulated shifts forces many frequency-consistent additive
parallelograms. This estimates coherence but does not yet integrate the graph. -/
theorem correlation_fourth_le_graphEnergy (H : Finset G) (b : G → ℂ)
    (ξ : G → AddChar G ℂ) (f : G → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hb : ∀ h, ‖b h‖ ≤ 1) (hsupp : ∀ h, h ∉ H → b h = 0) :
    ‖𝔼 h, b h*hat (derivative f h) (ξ h)‖^4 ≤ graphEnergy H ξ := by
  have hident : (𝔼 h, b h*hat (derivative f h) (ξ h)) =
      𝔼 x, 𝔼 y, conj (f x)*shiftKernel b ξ x y*f y := by
    unfold hat derivative
    simp_rw [mul_expect]
    rw [expect_comm]
    apply expect_congr rfl
    intro x _
    calc
      _ = 𝔼 h, conj (f x)*shiftKernel b ξ x (x+h)*f (x+h) := by
        apply expect_congr rfl
        intro h _
        simp only [shiftKernel,add_sub_cancel_left]
        ring
      _ = _ := Fintype.expect_equiv (Equiv.addLeft x) _ _ (fun _ ↦ rfl)
  rw [hident]
  calc
    _ ≤ 𝔼 y, 𝔼 z, ‖𝔼 x, shiftKernel b ξ x y*conj (shiftKernel b ξ x z)‖^2 :=
      kernel_fourth_bound _ _ _ (fun x ↦ by simpa only [Complex.norm_conj] using hf x) hf
    _ = _ := kernel_gram_shift _
    _ ≤ graphEnergy H ξ := by
      apply expect_le_expect
      intro h _
      apply expect_le_expect
      intro k _
      apply expect_le_expect
      intro t _
      exact shifted_quadruple_re_le H b ξ hb hsupp h k t

lemma exists_phase_alignment (z : ℂ) : ∃ b : ℂ, ‖b‖ ≤ 1 ∧ b*z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · exact ⟨0,by norm_num,by simp [hz]⟩
  have hnorm : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hnormC : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hnorm
  refine ⟨conj z/(‖z‖ : ℂ),?_,?_⟩
  · simp only [norm_div,Complex.norm_conj,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _),div_self hnorm,le_refl]
  · rw [div_mul_eq_mul_div,mul_comm (conj z),Complex.mul_conj,
      Complex.normSq_eq_norm_sq,Complex.ofReal_pow,pow_two,mul_div_cancel_right₀ _ hnormC]

/-- The first coherence stage of the U³ inverse argument. Large U³ yields a
large derivative-frequency graph with polynomially large additive energy and
uniformly large derivative Fourier coefficients on its domain. -/
theorem large_U3_spectral_graph (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (hU : δ ≤ uniformityPower 2 f) :
    ∃ H : Finset G, ∃ ξ : G → AddChar G ℂ,
      δ/2*(Fintype.card G : ℝ) ≤ H.card ∧
      (∀ h ∈ H, δ/2 ≤ ‖hat (derivative f h) (ξ h)‖^2) ∧
      (δ/2)^4 ≤ graphEnergy H ξ := by
  let v : G → ℝ := fun h ↦ uniformityPower 1 (derivative f h)
  have hv (h : G) : 0 ≤ v h ∧ v h ≤ 1 :=
    ⟨uniformityPower_nonneg _ _,uniformityPower_le_one _ _ (derivative_norm_le_one f hf h)⟩
  have hfreq (h : G) := exists_large_fourier (derivative f h) (derivative_norm_le_one f hf h)
  choose ξ hξ using hfreq
  let a : G → ℂ := fun h ↦ hat (derivative f h) (ξ h)
  have ha (h : G) : ‖a h‖ ≤ 1 := norm_hat_le_one _ (derivative_norm_le_one f hf h) _
  have hvnorm (h : G) : v h ≤ ‖a h‖ := by
    have hh := hξ h
    change v h ≤ ‖a h‖^2 at hh
    nlinarith [ha h,norm_nonneg (a h)]
  let H := univ.filter (fun h ↦ δ/2 ≤ v h)
  have havg : δ ≤ 𝔼 h, v h := hU
  have hmany := dense_high_values v hv hδ havg
  have halign (h : G) := exists_phase_alignment (a h)
  choose c hc hcprod using halign
  let b : G → ℂ := fun h ↦ if h ∈ H then c h else 0
  have hb (h : G) : ‖b h‖ ≤ 1 := by
    dsimp [b]
    split_ifs
    · exact hc h
    · norm_num
  have hbzero (h : G) (hh : h ∉ H) : b h = 0 := if_neg hh
  have hcorr : (𝔼 h, b h*a h) = ((𝔼 h, if h ∈ H then ‖a h‖ else 0 : ℝ) : ℂ) := by
    rw [ofReal_expect]
    apply expect_congr rfl
    intro h _
    by_cases hh : h ∈ H
    · simp only [b,if_pos hh,hcprod]
    · simp only [b,if_neg hh,zero_mul,Complex.ofReal_zero]
  have hnonneg : 0 ≤ 𝔼 h, if h ∈ H then ‖a h‖ else 0 :=
    expect_nonneg (fun h _ ↦ by split_ifs <;> positivity)
  have hcorrLower : δ/2 ≤ 𝔼 h, if h ∈ H then ‖a h‖ else 0 := by
    have hpt (h : G) : v h ≤ (if h ∈ H then ‖a h‖ else 0)+δ/2 := by
      by_cases hh : h ∈ H
      · rw [if_pos hh]; linarith [hvnorm h]
      · have hh' : v h < δ/2 := by
          simpa only [H,mem_filter,mem_univ,true_and,not_le] using hh
        rw [if_neg hh]; linarith
    have hh := expect_le_expect (fun h (_ : h ∈ univ) ↦ hpt h)
    rw [expect_add_distrib,Fintype.expect_const] at hh
    linarith
  refine ⟨H,ξ,?_,?_,?_⟩
  · exact (le_div_iff₀ (by exact_mod_cast Fintype.card_pos : (0 : ℝ) < Fintype.card G)).mp hmany
  · intro h hh
    exact ((mem_filter.mp hh).2).trans (hξ h)
  · have hh := correlation_fourth_le_graphEnergy H b ξ f hf hb hbzero
    change ‖𝔼 h, b h*a h‖^4 ≤ _ at hh
    rw [hcorr,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hnonneg] at hh
    exact (pow_le_pow_left₀ (by positivity) hcorrLower 4).trans hh

/-- The coherence estimate also applies to polynomially many higher derivative
slices. The individual frequency graphs still need to be integrated and made
compatible across slices before this can yield a higher-order inverse theorem. -/
theorem many_derivative_spectral_graphs (n : ℕ) (f : G → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) {δ : ℝ} (hδ : 0 ≤ δ)
    (hU : δ ≤ uniformityPower (n+2) f) :
    ∃ T : Finset (Fin n → G),
      δ/2*(Fintype.card G : ℝ)^n ≤ T.card ∧
      ∀ h ∈ T, ∃ H : Finset G, ∃ ξ : G → AddChar G ℂ,
        δ/4*(Fintype.card G : ℝ) ≤ H.card ∧
        (∀ t ∈ H, δ/4 ≤ ‖hat (derivative (iterDerivative f h) t) (ξ t)‖^2) ∧
        (δ/4)^4 ≤ graphEnergy H ξ := by
  let v : (Fin n → G) → ℝ := fun h ↦ uniformityPower 2 (iterDerivative f h)
  have hv (h : Fin n → G) : 0 ≤ v h ∧ v h ≤ 1 :=
    ⟨uniformityPower_nonneg _ _,uniformityPower_le_one _ _ (iterDerivative_norm_le_one f hf h)⟩
  have havg : δ ≤ 𝔼 h, v h := by simpa only [uniformityPower_iterDerivative n 2] using hU
  let T := univ.filter (fun h ↦ δ/2 ≤ v h)
  refine ⟨T,?_,?_⟩
  · have hh := dense_high_values v hv hδ havg
    have hc : (0 : ℝ) < Fintype.card (Fin n → G) := by exact_mod_cast Fintype.card_pos
    have hh' := (le_div_iff₀ hc).mp hh
    simpa only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,T] using hh'
  · intro h hh
    have hslice : δ/2 ≤ uniformityPower 2 (iterDerivative f h) := (mem_filter.mp hh).2
    have he : δ/2/2 = δ/4 := by ring
    simpa only [he] using large_U3_spectral_graph (iterDerivative f h)
      (iterDerivative_norm_le_one f hf h) (by positivity) hslice

#print axioms kernel_fourth_bound
#print axioms correlation_fourth_le_graphEnergy
#print axioms large_U3_spectral_graph
#print axioms many_derivative_spectral_graphs
end Erdos3SpectralGraphEnergy
