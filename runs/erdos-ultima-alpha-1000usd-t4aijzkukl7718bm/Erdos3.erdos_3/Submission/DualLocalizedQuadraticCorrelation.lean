import Submission.AveragedLocalizedQuadraticCorrelation

/-! Extracting a coefficient of the Bohr-supported side of mixed correlation
retains normalized local correlation, without a Bohr-density loss. -/
namespace Erdos3DualLocalizedQuadraticCorrelation
open Finset Erdos3FiniteFourier Erdos3FiniteUniformity Erdos3TwistedCorrelationEnergy
  Erdos3LinearFormsUniformity Erdos3MixedCorrelationFourier Erdos3CorrelationSifting
  Erdos3LocalizedQuadraticCorrelation
open scoped BigOperators Classical Pointwise ComplexConjugate
set_option maxHeartbeats 5000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma exists_second_coefficient_from_mixed_energy (a b : G → ℂ) :
    ∃ χ : AddChar G ℂ, (𝔼 h, ‖mixedCorr a b h‖^2) ≤
      ‖hat b χ‖^2*(𝔼 x, ‖a x‖^2) := by
  obtain ⟨χ,_,hχ⟩ := exists_max_image univ (fun χ : AddChar G ℂ ↦ ‖hat b χ‖^2) univ_nonempty
  refine ⟨χ,?_⟩
  rw [mixedCorr_energy,← parseval,mul_sum]
  apply sum_le_sum
  intro ψ hψ
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hχ ψ hψ) (sq_nonneg ‖hat a ψ‖)

/-- A local Fourier coefficient of b has normalized squared magnitude at least
kappa*density(H). There is NO factor density(Q) in this normalized conclusion. -/
theorem localized_mixed_inverse_second (H Q : Finset G) (hH : H.Nonempty) (hQ : Q.Nonempty)
    (a b : G → ℂ) (ha : ∀ x, ‖a x‖ ≤ 1) {κ : ℝ}
    (hmean : κ ≤ 𝔼 h : H, ‖𝔼 x : Q, a ((x : G)+h)*conj (b x)‖^2) :
    ∃ χ : AddChar G ℂ, κ*density H ≤ ‖𝔼 x : Q, b x*conj (χ x)‖^2 := by
  let bQ : G → ℂ := fun x ↦ if x ∈ Q then b x else 0
  have hσQ : 0 < density Q := density_pos Q hQ
  have hσH : 0 < density H := density_pos H hH
  have he (h : G) : ‖mixedCorr a bQ h‖^2 =
      (density Q)^2*‖𝔼 x : Q, a ((x : G)+h)*conj (b x)‖^2 := by
    rw [mixedCorr_mask Q hQ a b h,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hσQ,mul_pow]
  have hl : κ*density H*(density Q)^2 ≤ 𝔼 h, ‖mixedCorr a bQ h‖^2 := by
    have hh := density_mul_subset_expect_le H hH (fun h ↦ ‖mixedCorr a bQ h‖^2) (fun _ ↦ sq_nonneg _)
    simp_rw [he] at hh
    rw [← mul_expect] at hh
    have hm := mul_le_mul_of_nonneg_left hmean (mul_nonneg hσH.le (sq_nonneg (density Q)))
    simp_rw [he]
    nlinarith only [hm,hh]
  have hmass : (𝔼 x, ‖a x‖^2) ≤ 1 := by
    apply expect_le univ_nonempty
    intro x _
    nlinarith [ha x,norm_nonneg (a x)]
  obtain ⟨χ,hχ⟩ := exists_second_coefficient_from_mixed_energy a bQ
  have hh := hl.trans (hχ.trans (mul_le_mul_of_nonneg_left hmass (sq_nonneg _)))
  rw [mul_one] at hh
  have hhat : hat bQ χ = (density Q : ℂ)*(𝔼 x : Q, b x*conj (χ x)) := by
    rw [← complex_masked_expect Q hQ (fun x ↦ b x*conj (χ x))]
    unfold hat bQ
    apply expect_congr rfl
    intro x _
    split_ifs <;> simp_all only [zero_mul]
  rw [hhat,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hσQ,mul_pow] at hh
  refine ⟨χ,?_⟩
  nlinarith only [hh,sq_pos_of_pos hσQ]

variable [DecidableEq G]

/-- The normalized correlation is now extracted on Q, the small base domain,
while the direction set H need not be small. -/
theorem averaged_dual_localized_phase_correlation (H Q R : Finset G) (hH : H.Nonempty) (hQ : Q.Nonempty)
    (hR : Q+H ⊆ R) (u v q : G → ℂ) (F : G → AddChar G ℂ)
    (hu : ∀ x, ‖u x‖ ≤ 1) (hv : ∀ x, ‖v x‖ ≤ 1) (hq : ∀ x, ‖q x‖ = 1)
    {κ e : ℝ} (hecost : 4*e^2 ≤ κ)
    (hc : κ ≤ 𝔼 h : H, ‖mixedCoefficient u v F h‖^2)
    (happrox : ∀ h ∈ H, ∀ x ∈ Q, ‖derivative q h x-q h*F h x‖ ≤ e) :
    ∃ χ : G → AddChar G ℂ, (κ/4)*density H ≤
      𝔼 z, ‖𝔼 y : Q, v (z+y)*conj (q y)*conj (χ z y)‖^2 := by
  letI : Nonempty H := hH.to_subtype
  have hmeanloc : κ ≤ 𝔼 z, 𝔼 h : H, ‖localizedMixed Q u v F z h‖^2 := by
    have hh (h : G) : ‖mixedCoefficient u v F h‖^2 ≤ 𝔼 z, ‖localizedMixed Q u v F z h‖^2 := by
      rw [← localizedMixed_mean Q hQ u v F h]
      exact mean_product_sq_le _ _ (fun z ↦ by simp only [Complex.norm_conj,AddChar.norm_apply,le_refl])
    have hh' := hc.trans (expect_le_expect (fun h _ ↦ hh h))
    rwa [expect_comm] at hh'
  let a : G → G → ℂ := fun z y ↦ if y ∈ R then u (z+y)*conj (q y) else 0
  let b : G → G → ℂ := fun z x ↦ v (z+x)*conj (q x)
  let r : G → G → ℂ := fun z h ↦ 𝔼 x : Q, a z ((x : G)+h)*conj (b z x)
  have ha (z x : G) : ‖a z x‖ ≤ 1 := by
    dsimp only [a]
    split_ifs
    · simpa only [norm_mul,Complex.norm_conj,hq,mul_one] using hu (z+x)
    · norm_num
  have herr (z : G) (h : H) : ‖localizedMixed Q u v F z h-q h*r z h‖ ≤ e :=
    localized_detwist_error H Q R hQ hR u v q F hu hv hq happrox z h.property
  have hsq (z : G) (h : H) : ‖localizedMixed Q u v F z h‖^2 ≤ 2*‖r z h‖^2+2*e^2 := by
    have hn : ‖localizedMixed Q u v F z h‖ ≤ e+‖r z h‖ := by
      calc
        _ = ‖(localizedMixed Q u v F z h-q h*r z h)+q h*r z h‖ := by congr 1; ring
        _ ≤ ‖localizedMixed Q u v F z h-q h*r z h‖+‖q h*r z h‖ := norm_add_le _ _
        _ ≤ _ := by simpa only [norm_mul,hq,one_mul] using add_le_add (herr z h) (le_refl ‖r z h‖)
    have hp := pow_le_pow_left₀ (norm_nonneg _) hn 2
    nlinarith [sq_nonneg (e-‖r z h‖)]
  have hmean : κ/4 ≤ 𝔼 z, 𝔼 h : H, ‖r z h‖^2 := by
    have hh := hmeanloc.trans (expect_le_expect (fun z _ ↦ expect_le_expect (fun h _ ↦ hsq z h)))
    simp only [expect_add_distrib,← mul_expect,Fintype.expect_const] at hh
    linarith
  have hχ (z : G) : ∃ χ : AddChar G ℂ,
      (𝔼 h : H, ‖r z h‖^2)*density H ≤ ‖𝔼 y : Q, b z y*conj (χ y)‖^2 :=
    localized_mixed_inverse_second H Q hH hQ (a z) (b z) (ha z) le_rfl
  choose χ hχ using hχ
  refine ⟨χ,?_⟩
  calc
    _ ≤ (𝔼 z, 𝔼 h : H, ‖r z h‖^2)*density H :=
      mul_le_mul_of_nonneg_right hmean (density_pos H hH).le
    _ = 𝔼 z, (𝔼 h : H, ‖r z h‖^2)*density H := expect_mul _ _ _
    _ ≤ _ := expect_le_expect (fun z _ ↦ hχ z)

#print axioms localized_mixed_inverse_second
#print axioms averaged_dual_localized_phase_correlation
end Erdos3DualLocalizedQuadraticCorrelation
