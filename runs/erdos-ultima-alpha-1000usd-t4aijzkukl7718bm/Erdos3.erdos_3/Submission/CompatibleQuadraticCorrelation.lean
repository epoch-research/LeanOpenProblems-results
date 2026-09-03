import Submission.UnlocalizedSkewSymmetry

/-! Reusable local quadratic correlation from a compatible map. No assumption
that its original correlated direction set lies in a Bohr domain is needed. -/
namespace Erdos3CompatibleQuadraticCorrelation
open Finset Erdos3FiniteUniformity Erdos3FiniteFourier Erdos3FiniteBohr Erdos3BohrCovering
  Erdos3LocalPhaseDuality Erdos3TwistedCorrelationEnergy Erdos3LocalQuadraticIntegration
  Erdos3U3ApproximateSymmetry Erdos3DoubledBohrLocalization Erdos3LocalizedQuadraticCorrelation
  Erdos3CorrelationSifting Erdos3U3LocalQuadraticCorrelation Erdos3LocalQuadraticInverse
open scoped BigOperators Classical Pointwise ComplexConjugate
set_option maxHeartbeats 6000000

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The correlated directions need not already lie in the integration domain;
recentered doubled-Bohr localization and both fixed offsets are handled exactly. -/
theorem compatible_quadratic_correlation
    (h2 : Function.Bijective (fun x : G ↦ x+x))
    (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (T : Finset G) (hT : T.Nonempty) (F : G → AddChar G ℂ)
    (a₀ : G) (χ₀ : AddChar G ℂ) (E : Finset (AddChar G ℂ))
    (hadd : LocallyAdditive (bohr E (1/2) : Set G) F)
    (hdiff : ∀ s ∈ T, ∀ t ∈ T, F (s-t) = F s-F t)
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hcoef : ∀ t ∈ T, κ ≤ ‖hat (derivative f (t+a₀)) (F t+χ₀)‖^2)
    (hsym : ∀ x ∈ bohr E (1/2), ∀ y ∈ bohr E (1/2), ‖F x y-F y x‖ ≤ κ/8) :
    ∃ q : G → ℂ, ∃ a : G, (∀ x, ‖q x‖ = 1) ∧
      IsLocallyQuadratic (doubledBohr E (1/8) : Set G) q ∧
      κ*density T/(4*(8385 : ℝ)^(2*E.card)) ≤
        ‖𝔼 y, if y ∈ doubledBohr E (1/8) then f (a+y)*conj (q y) else 0‖^2 := by
  let Q := doubledBohr E (1/16)
  let R := doubledBohr E (1/8)
  have hQ : Q.Nonempty := doubledBohr_nonempty E (by norm_num)
  obtain ⟨H,t₀,hH0,hHsub,hHsize,ht₀,hHT⟩ := exists_doubled_bohr_restriction h2 E T hT
  have hH : H.Nonempty := ⟨0,hH0⟩
  have hR : Q+H ⊆ R := by
    intro x hx
    obtain ⟨y,hy,h,hh,rfl⟩ := mem_add.mp hx
    simpa only [show (1/16 : ℝ)+1/16 = 1/8 by norm_num] using doubledBohr_add E hy (hHsub hh)
  let q : G → ℂ := Erdos3LocalQuadraticIntegration.quadraticPhase F (halfHom h2)
  let u : G → ℂ := fun x ↦ f (x+(a₀+t₀))
  let v : G → ℂ := fun x ↦ f x*(F t₀+χ₀) x
  have hu (x : G) : ‖u x‖ ≤ 1 := hf _
  have hv (x : G) : ‖v x‖ ≤ 1 := by
    simpa only [v,norm_mul,AddChar.norm_apply,mul_one] using hf x
  have hq (x : G) : ‖q x‖ = 1 := quadraticPhase_norm F (halfHom h2) x
  have hc (h : G) (hh : h ∈ H) : κ ≤ ‖mixedCoefficient u v F h‖^2 := by
    rw [shifted_mixed_coefficient]
    have hhF : F h = F (h+t₀)-F t₀ := by
      simpa only [add_sub_cancel_right] using hdiff (h+t₀) (hHT h hh) t₀ ht₀
    rw [hhF,show F (h+t₀)-F t₀+(F t₀+χ₀) = F (h+t₀)+χ₀ by abel,
      show h+(a₀+t₀) = (h+t₀)+a₀ by abel]
    exact hcoef (h+t₀) (hHT h hh)
  have hmean : κ ≤ 𝔼 h : H, ‖mixedCoefficient u v F h‖^2 := by
    letI : Nonempty H := hH.to_subtype
    exact le_expect univ_nonempty (fun h _ ↦ hc h h.property)
  have happrox (h : G) (hh : h ∈ H) (x : G) (hx : x ∈ Q) :
      ‖derivative q h x-q h*F h x‖ ≤ κ/4 := by
    have hxhalf : halfHom h2 x ∈ bohr E (1/8) := bohr_mono E (by norm_num : (1/16 : ℝ) ≤ 1/8)
      ((mem_doubledBohr h2 E (1/16) x).mp hx)
    have hhhalf : halfHom h2 h ∈ bohr E (1/8) := bohr_mono E (by norm_num : (1/16 : ℝ) ≤ 1/8)
      ((mem_doubledBohr h2 E (1/16) h).mp (hHsub hh))
    have hp := integrated_derivative_on_refined_bohr E E F hadd (halfHom h2)
      (halfHom_double h2) hsym
      (by simpa only [union_self] using hxhalf) (by simpa only [union_self] using hhhalf)
    simpa only [double_halfHom,show 2*(κ/8) = κ/4 by ring] using hp
  have hecost : 4*(κ/4)^2 ≤ κ := by nlinarith [mul_nonneg hκ.le (sub_nonneg.mpr hκ1)]
  obtain ⟨z,χ,hcorr⟩ := localized_phase_correlation H Q R hH hQ hR u v q F hu hv hq
    (by positivity : 0 ≤ κ/4) hecost hmean happrox
  have hprod : density T/(8385 : ℝ)^(2*E.card) ≤ density H*density Q :=
    density_product_from_card E T H Q hHsize (doubled_small_card h2 E)
  have hlower : κ*density T/(4*(8385 : ℝ)^(2*E.card)) ≤ (κ/4)*density H*density Q := by
    have hh := mul_le_mul_of_nonneg_left hprod (show 0 ≤ κ/4 by positivity)
    convert hh using 1 <;> ring
  let q' : G → ℂ := fun y ↦ q y*χ y
  have hq' (x : G) : ‖q' x‖ = 1 := by simp only [q',norm_mul,hq,AddChar.norm_apply,mul_one]
  have hRsmall : R ⊆ bohr E (1/4) := by
    intro x hx
    simpa only [show (2 : ℝ)*(1/8) = 1/4 by norm_num] using doubledBohr_subset E (1/8) hx
  have hquad : IsLocallyQuadratic (R : Set G) q' :=
    (integrated_phase_local_quadratic E F hadd (halfHom h2) hRsmall).mul_character χ
  refine ⟨q',z+(a₀+t₀),hq',hquad,hlower.trans ?_⟩
  convert hcorr using 1
  congr 2
  apply expect_congr rfl
  intro y _
  change (if y ∈ R then f (z+(a₀+t₀)+y)*conj (q' y) else 0) =
    (if y ∈ R then u (z+y)*conj (q y)*conj (χ y) else 0)
  by_cases hy : y ∈ R
  · simp only [if_pos hy,u,q',map_mul,mul_assoc]
    rw [show z+(a₀+t₀)+y = (z+y)+(a₀+t₀) by abel]
  · simp only [if_neg hy]

#print axioms compatible_quadratic_correlation
end Erdos3CompatibleQuadraticCorrelation
