import Submission.LocalizedBilinearExtraction

/-! Phase-preserving modulated correlation estimates. These retain the twisting
phase that was discarded in the unweighted frequency-graph energy bound. -/
namespace Erdos3TwistedCorrelationEnergy
open Finset Erdos3FiniteUniformity Erdos3FiniteFourier Erdos3QuadraticFourAPBarrier
  Erdos3SpectralGraphEnergy Erdos3LinearFormsUniformity
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 4000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def mixedCoefficient (u v : G → ℂ) (F : G → AddChar G ℂ) (h : G) : ℂ :=
  𝔼 x, u (x+h)*conj (v x)*conj (F h x)

noncomputable def twistedEnergy (b : G → ℂ) (F : G → AddChar G ℂ) : ℂ :=
  𝔼 h, 𝔼 k, 𝔼 t, b h*conj (b k)*conj (b (h-t))*b (k-t)*F (h-k) t

lemma character_sub_apply (χ ψ : AddChar G ℂ) (x : G) : (χ-ψ) x = χ x*conj (ψ x) := by
  change (χ*ψ⁻¹) x = _
  rw [AddChar.mul_apply,AddChar.inv_apply,AddChar.map_neg_eq_inv,AddChar.inv_apply_eq_conj]

/-- A phase-compatible frequency map makes the kernel Gram identity an exact
twisted energy identity. No absolute values of the twisting phase are taken. -/
lemma kernel_gram_eq_twistedEnergy (T : Finset G) (b : G → ℂ) (F : G → AddChar G ℂ)
    (hsupp : ∀ h, h ∉ T → b h = 0)
    (hF : ∀ h ∈ T, ∀ k ∈ T, F (h-k) = F h-F k) :
    (𝔼 y, 𝔼 z, ‖𝔼 x, shiftKernel b F x y*conj (shiftKernel b F x z)‖^2) =
      (twistedEnergy b F).re := by
  rw [kernel_gram_shift]
  unfold twistedEnergy
  simp only [expect_re]
  apply expect_congr rfl
  intro h _
  apply expect_congr rfl
  intro k _
  apply expect_congr rfl
  intro t _
  rw [← expect_re,shifted_quadruple_expect]
  by_cases hh : h ∈ T
  · by_cases hk : k ∈ T
    · by_cases hht : h-t ∈ T
      · by_cases hkt : k-t ∈ T
        · have hdiff : F (h-t)-F (k-t) = F h-F k := by
            rw [← hF (h-t) hht (k-t) hkt,show (h-t)-(k-t) = h-k by abel,hF h hh k hk]
          have heq : F h*F (k-t) = F k*F (h-t) := by
            change F h+F (k-t) = F k+F (h-t)
            have he := sub_eq_sub_iff_add_eq_add.mp hdiff
            simpa only [add_comm] using he.symm
          rw [if_pos heq,mul_one]
          have heval : F (h-t) t*conj (F (k-t) t) = F (h-k) t := by
            rw [← character_sub_apply,hdiff,← hF h hh k hk]
          congr 1
          calc
            _ = (b h*conj (b k)*conj (b (h-t))*b (k-t))*(F (h-t) t*conj (F (k-t) t)) := by ring
            _ = _ := by rw [heval]
        · simp only [hsupp _ hkt,mul_zero,zero_mul,Complex.zero_re]
      · simp only [hsupp _ hht,map_zero,mul_zero,zero_mul,Complex.zero_re]
    · simp only [hsupp _ hk,map_zero,mul_zero,zero_mul,Complex.zero_re]
  · simp only [hsupp _ hh,zero_mul,Complex.zero_re]

/-- The retained twisted energy is also an average of squared Fourier
coefficients of derivatives of the phase-alignment function, with opposite
frequencies. This identity holds for any F, even without local additivity. -/
theorem twistedEnergy_eq_derivative_fourier (b : G → ℂ) (F : G → AddChar G ℂ) :
    twistedEnergy b F = ((𝔼 a, ‖hat (derivative b a) (-F a)‖^2 : ℝ) : ℂ) := by
  have hinner (a t : G) :
      (𝔼 k, b (k+a)*conj (b k)*conj (b (k+a-t))*b (k-t)) = complexCorr (derivative b a) t := by
    calc
      _ = 𝔼 y, b (y+t+a)*conj (b (y+t))*conj (b (y+a))*b y :=
        (Fintype.expect_equiv (Equiv.addRight t) _ _ (fun y ↦ by simp only [Equiv.coe_addRight,add_sub_cancel_right,show y+t+a-t = y+a by abel])).symm
      _ = _ := by
        unfold complexCorr derivative
        apply expect_congr rfl
        intro y _
        simp only [map_mul,starRingEnd_self_apply]
        ring
  have hneg (a x : G) : conj ((-F a) x) = F a x := by
    change conj (((F a)⁻¹) x) = _
    rw [AddChar.inv_apply,AddChar.map_neg_eq_inv,AddChar.inv_apply_eq_conj,starRingEnd_self_apply]
  unfold twistedEnergy
  calc
    _ = 𝔼 k, 𝔼 h, 𝔼 t, b h*conj (b k)*conj (b (h-t))*b (k-t)*F (h-k) t := expect_comm _ _ _
    _ = 𝔼 k, 𝔼 a, 𝔼 t, b (k+a)*conj (b k)*conj (b (k+a-t))*b (k-t)*F a t := by
      apply expect_congr rfl
      intro k _
      exact (Fintype.expect_equiv (Equiv.addLeft k) _ _ (fun a ↦ by simp)).symm
    _ = 𝔼 a, 𝔼 k, 𝔼 t, b (k+a)*conj (b k)*conj (b (k+a-t))*b (k-t)*F a t := expect_comm _ _ _
    _ = 𝔼 a, 𝔼 t, complexCorr (derivative b a) t*F a t := by
      apply expect_congr rfl
      intro a _
      rw [expect_comm]
      apply expect_congr rfl
      intro t _
      rw [← expect_mul,hinner]
    _ = 𝔼 a, hat (complexCorr (derivative b a)) (-F a) := by simp only [hat,hneg]
    _ = _ := by simp only [hat_complexCorr,ofReal_expect]

/-- The phase-preserving two-Cauchy–Schwarz bound for mixed modulated shifts. -/
theorem mixed_correlation_fourth_le (T : Finset G) (b u v : G → ℂ) (F : G → AddChar G ℂ)
    (hu : ∀ x, ‖u x‖ ≤ 1) (hv : ∀ x, ‖v x‖ ≤ 1)
    (hsupp : ∀ h, h ∉ T → b h = 0)
    (hF : ∀ h ∈ T, ∀ k ∈ T, F (h-k) = F h-F k) :
    ‖𝔼 h, b h*mixedCoefficient u v F h‖^4 ≤
      𝔼 a, ‖hat (derivative b a) (-F a)‖^2 := by
  have he : (𝔼 h, b h*mixedCoefficient u v F h) =
      𝔼 x, 𝔼 y, conj (v x)*shiftKernel b F x y*u y := by
    unfold mixedCoefficient
    simp_rw [mul_expect]
    rw [expect_comm]
    apply expect_congr rfl
    intro x _
    calc
      _ = 𝔼 h, conj (v x)*shiftKernel b F x (x+h)*u (x+h) := by
        apply expect_congr rfl
        intro h _
        simp only [shiftKernel,add_sub_cancel_left]
        ring
      _ = _ := Fintype.expect_equiv (Equiv.addLeft x) _ _ (fun _ ↦ rfl)
  rw [he]
  have hh := kernel_fourth_bound (shiftKernel b F) (fun x ↦ conj (v x)) u
    (fun x ↦ by simpa only [Complex.norm_conj] using hv x) hu
  rw [kernel_gram_eq_twistedEnergy T b F hsupp hF,twistedEnergy_eq_derivative_fourier,Complex.ofReal_re] at hh
  exact hh

#print axioms twistedEnergy_eq_derivative_fourier
#print axioms mixed_correlation_fourth_le
end Erdos3TwistedCorrelationEnergy
