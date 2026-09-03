import Submission.CrossSpectralSymmetry
import Submission.BiasedDifferenceFiber
import Submission.DualLocalizedQuadraticCorrelation
import Submission.SmallBaseQuadraticIntegration

/-! Normalized quadratic correlation at any smaller positive Bohr radius.
The phase remains locally quadratic on the fixed larger domain. -/
namespace Erdos3VariableRadiusQuadraticCorrelation
open Finset Erdos3FiniteUniformity Erdos3FiniteFourier Erdos3FiniteBohr Erdos3BohrCovering
  Erdos3LocalPhaseDuality Erdos3TwistedCorrelationEnergy Erdos3LocalQuadraticIntegration
  Erdos3DoubledBohrLocalization Erdos3CorrelationSifting Erdos3LocalQuadraticInverse
  Erdos3UnlocalizedBilinearExtraction Erdos3BiasedSkewDifferences Erdos3BiasedDifferenceFiber
  Erdos3DualLocalizedQuadraticCorrelation Erdos3SmallBaseQuadraticIntegration
  Erdos3QuantitativeSkewSymmetry
open scoped BigOperators Classical Pointwise ComplexConjugate
set_option maxHeartbeats 6000000
set_option maxRecDepth 3000

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The averaging radius may be chosen after E is known, without weakening
the correlation. Local quadraticity holds on the whole fixed outer domain. -/
theorem variable_radius_compatible_quadratic_correlation
    (h2 : Function.Bijective (fun x : G ↦ x+x)) (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (T : Finset G) (hT : T.Nonempty) (F : G → AddChar G ℂ)
    (a₀ : G) (χ₀ : AddChar G ℂ) (E : Finset (AddChar G ℂ))
    (hF : LocallyAdditive (diffBall T 4 : Set G) F)
    (hdiff : ∀ s ∈ T, ∀ t ∈ T, F (s-t) = F s-F t)
    (hE : bohr E (1/2) ⊆ diffBall T 2)
    {ρ : ℝ} (hρ : 0 < ρ) (hρmax : ρ ≤ 1/16)
    {κ Λ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hΛ : 0 < Λ) (hΛmean : Λ ≤ pairSkewBias T F)
    (hcoef : ∀ t ∈ T, κ ≤ ‖hat (derivative f (t+a₀)) (F t+χ₀)‖^2)
    (hsym : ∀ x ∈ bohr E (1/2), ∀ d : G, Λ/2 ≤ normalizedSkewBias T F d → ‖F x d-F d x‖ ≤ κ/4) :
    ∃ q : G → G → ℂ, (∀ a x, ‖q a x‖ = 1) ∧
      (∀ a, IsLocallyQuadratic (doubledBohr E (1/16) : Set G) (q a)) ∧
      κ*Λ*density T/8 ≤ 𝔼 a, ‖𝔼 y : doubledBohr E ρ, f (a+y)*conj (q a y)‖^2 := by
  obtain ⟨t₀,ht₀,H,hH,hHT,hHsize,hbias⟩ := exists_biased_difference_fiber T hT
    (normalizedSkewBias T F) (normalizedSkewBias_le_one T F) hΛ hΛmean
  let Q := doubledBohr E ρ
  let R := diffBall T 3
  have hQ : Q.Nonempty := doubledBohr_nonempty E hρ.le
  have hQsmall : Q ⊆ bohr E (1/8) := by
    exact (doubledBohr_subset E ρ).trans (bohr_mono E (by linarith))
  have hQtwo : Q ⊆ diffBall T 2 := hQsmall.trans ((bohr_mono E (by norm_num : (1/8 : ℝ) ≤ 1/2)).trans hE)
  have hHone : H ⊆ diffBall T 1 := fun _ hh ↦ mem_diffBall_one.mpr (hHT hh)
  have hR : Q+H ⊆ R := by
    intro z hz
    obtain ⟨x,hx,h,hh,rfl⟩ := mem_add.mp hz
    exact diffBall_add (hQtwo hx) (hHone hh)
  let q : G → ℂ := Erdos3LocalQuadraticIntegration.quadraticPhase F (halfHom h2)
  let ψ : AddChar G ℂ := F t₀+χ₀
  let u : G → ℂ := fun x ↦ f (x+(a₀+t₀))
  let v : G → ℂ := fun x ↦ f x*ψ x
  have hu (x : G) : ‖u x‖ ≤ 1 := hf _
  have hv (x : G) : ‖v x‖ ≤ 1 := by simpa only [v,norm_mul,AddChar.norm_apply,mul_one] using hf x
  have hq (x : G) : ‖q x‖ = 1 := quadraticPhase_norm F (halfHom h2) x
  have hc (h : G) (hh : h ∈ H) : κ ≤ ‖mixedCoefficient u v F h‖^2 := by
    rw [shifted_mixed_coefficient]
    have hhF : F h = F (h+t₀)-F t₀ := by
      simpa only [add_sub_cancel_right] using hdiff (h+t₀) (hbias h hh).1 t₀ ht₀
    change κ ≤ ‖hat (derivative f (h+(a₀+t₀))) (F h+(F t₀+χ₀))‖^2
    rw [hhF,show F (h+t₀)-F t₀+(F t₀+χ₀) = F (h+t₀)+χ₀ by abel,
      show h+(a₀+t₀) = (h+t₀)+a₀ by abel]
    exact hcoef (h+t₀) (hbias h hh).1
  have hmean : κ ≤ 𝔼 h : H, ‖mixedCoefficient u v F h‖^2 := by
    letI : Nonempty H := hH.to_subtype
    exact le_expect univ_nonempty (fun h _ ↦ hc h h.property)
  have happrox (h : G) (hh : h ∈ H) (x : G) (hx : x ∈ Q) :
      ‖derivative q h x-q h*F h x‖ ≤ κ/4 := by
    have hxhalf : halfHom h2 x ∈ bohr E (1/2) := bohr_mono E (by linarith : ρ ≤ 1/2)
      ((mem_doubledBohr h2 E ρ x).mp hx)
    have huP := diffBall_mono T hT (by decide : 2 ≤ 4) (hE hxhalf)
    have hxP := diffBall_mono T hT (by decide : 2 ≤ 4) (hQtwo hx)
    have hhP := diffBall_mono T hT (by decide : 1 ≤ 4) (hHone hh)
    have hsumP := diffBall_mono T hT (by decide : 3 ≤ 4) (hR (add_mem_add hx hh))
    have hp := quadraticPhase_derivative_small_base hF (halfHom h2) (halfHom_double h2)
      huP (by simpa only [double_halfHom] using hxP) hhP
      (by simpa only [double_halfHom] using hsumP) (hsym _ hxhalf h (hbias h hh).2)
    simpa only [double_halfHom] using hp
  have hecost : 4*(κ/4)^2 ≤ κ := by nlinarith [mul_nonneg hκ.le (sub_nonneg.mpr hκ1)]
  obtain ⟨χ,hcorr⟩ := averaged_dual_localized_phase_correlation H Q R hH hQ hR u v q F
    hu hv hq hecost hmean happrox
  have hHlow := density_lower_of_difference_card T H Λ hHsize
  have hlower : κ*Λ*density T/8 ≤ (κ/4)*density H := by
    have hh := mul_le_mul_of_nonneg_left hHlow (show 0 ≤ κ/4 by positivity)
    convert hh using 1 <;> ring
  have hadd : LocallyAdditive (bohr E (1/2) : Set G) F := by
    intro x hx y hy hxy
    exact hF x (diffBall_mono T hT (by decide) (hE hx)) y
      (diffBall_mono T hT (by decide) (hE hy)) (diffBall_mono T hT (by decide) (hE hxy))
  let q' : G → G → ℂ := fun a y ↦ q y*(χ a-ψ) y
  have hq' (a x : G) : ‖q' a x‖ = 1 := by simp only [q',norm_mul,hq,AddChar.norm_apply,mul_one]
  have hQouter : doubledBohr E (1/16) ⊆ bohr E (1/4) :=
    (doubledBohr_subset E (1/16)).trans (bohr_mono E (by norm_num))
  have hquad (a : G) : IsLocallyQuadratic (doubledBohr E (1/16) : Set G) (q' a) :=
    (integrated_phase_local_quadratic E F hadd (halfHom h2) hQouter).mul_character (χ a-ψ)
  refine ⟨q',hq',hquad,hlower.trans (hcorr.trans_eq ?_)⟩
  apply expect_congr rfl
  intro a _
  have he : (𝔼 y : Q, v (a+y)*conj (q y)*conj (χ a y)) =
      ψ a*(𝔼 y : Q, f (a+y)*conj (q' a y)) := by
    rw [mul_expect]
    apply expect_congr rfl
    intro y _
    simp only [v,q',AddChar.map_add_eq_mul,AddChar.sub_apply,AddChar.map_neg_eq_inv,
      AddChar.inv_apply_eq_conj,map_mul,starRingEnd_self_apply]
    ring
  rw [he,norm_mul,AddChar.norm_apply,one_mul]

#print axioms variable_radius_compatible_quadratic_correlation
end Erdos3VariableRadiusQuadraticCorrelation
