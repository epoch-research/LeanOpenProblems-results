import Submission.LocalizedQuadraticCorrelation

/-! Retaining the average over base translations in the local quadratic
correlation argument. This allows later positive, rather than signed, increments. -/
namespace Erdos3AveragedLocalizedQuadraticCorrelation
open Finset Erdos3FiniteFourier Erdos3FiniteUniformity Erdos3TwistedCorrelationEnergy
  Erdos3LinearFormsUniformity Erdos3MixedCorrelationFourier Erdos3CorrelationSifting
  Erdos3LocalizedQuadraticCorrelation
open scoped BigOperators Classical Pointwise ComplexConjugate
set_option maxHeartbeats 5000000

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Local integration supplies a linear-character correction at every center;
the squared masked correlations are large on average over those centers. -/
theorem averaged_localized_phase_correlation (H Q R : Finset G) (hH : H.Nonempty) (hQ : Q.Nonempty)
    (hR : Q+H ⊆ R) (u v q : G → ℂ) (F : G → AddChar G ℂ)
    (hu : ∀ x, ‖u x‖ ≤ 1) (hv : ∀ x, ‖v x‖ ≤ 1) (hq : ∀ x, ‖q x‖ = 1)
    {κ e : ℝ} (he : 0 ≤ e) (hecost : 4*e^2 ≤ κ)
    (hc : κ ≤ 𝔼 h : H, ‖mixedCoefficient u v F h‖^2)
    (happrox : ∀ h ∈ H, ∀ x ∈ Q, ‖derivative q h x-q h*F h x‖ ≤ e) :
    ∃ χ : G → AddChar G ℂ, (κ/4)*density H*density Q ≤
      𝔼 z, ‖𝔼 y, if y ∈ R then u (z+y)*conj (q y)*conj (χ z y) else 0‖^2 := by
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
  have hb (z x : G) : ‖b z x‖ ≤ 1 := by
    simpa only [b,norm_mul,Complex.norm_conj,hq,mul_one] using hv (z+x)
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
      (𝔼 h : H, ‖r z h‖^2)*density H*density Q ≤ ‖hat (a z) χ‖^2 :=
    localized_mixed_inverse H Q hH hQ (a z) (b z) (hb z) le_rfl
  choose χ hχ using hχ
  refine ⟨χ,?_⟩
  have hp : (κ/4)*density H*density Q ≤ 𝔼 z, ‖hat (a z) (χ z)‖^2 := by
    calc
      _ ≤ (𝔼 z, 𝔼 h : H, ‖r z h‖^2)*density H*density Q :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmean (density_pos H hH).le) (density_pos Q hQ).le
      _ = 𝔼 z, (𝔼 h : H, ‖r z h‖^2)*density H*density Q := by rw [expect_mul,expect_mul]
      _ ≤ _ := expect_le_expect (fun z _ ↦ hχ z)
  convert hp using 1
  apply expect_congr rfl
  intro z _
  congr 2
  unfold hat
  apply expect_congr rfl
  intro y _
  by_cases hy : y ∈ R <;> simp [a,hy]

#print axioms averaged_localized_phase_correlation
end Erdos3AveragedLocalizedQuadraticCorrelation
