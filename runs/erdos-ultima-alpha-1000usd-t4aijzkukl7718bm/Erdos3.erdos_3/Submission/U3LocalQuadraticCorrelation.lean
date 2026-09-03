import Submission.DoubledBohrLocalization

/-! A quantitative local quadratic correlation theorem from large U³ in a
finite abelian group with bijective doubling. This does not address higher
uniformity orders or the reciprocal-summability density-increment gap. -/
namespace Erdos3U3LocalQuadraticCorrelation
open Finset Erdos3FiniteUniformity Erdos3FiniteFourier Erdos3FiniteBohr Erdos3BohrCovering
  Erdos3LocalBilinearExtraction Erdos3LocalPhaseDuality Erdos3TwistedCorrelationEnergy
  Erdos3LocalQuadraticIntegration Erdos3QuantitativeSkewSymmetry Erdos3U3ApproximateSymmetry
  Erdos3DoubledBohrLocalization Erdos3LocalizedQuadraticCorrelation Erdos3CorrelationSifting
open scoped BigOperators Classical Pointwise ComplexConjugate
set_option maxHeartbeats 6000000

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

lemma density_product_from_card (C : Finset (AddChar G ℂ)) (T H Q : Finset G)
    (hH : T.card ≤ 129^(2*C.card)*H.card)
    (hQ : Fintype.card G ≤ 65^(2*C.card)*Q.card) :
    density T/(8385 : ℝ)^(2*C.card) ≤ density H*density Q := by
  have hN : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hHr : (T.card : ℝ) ≤ (129 : ℝ)^(2*C.card)*H.card := by exact_mod_cast hH
  have hQr : (Fintype.card G : ℝ) ≤ (65 : ℝ)^(2*C.card)*Q.card := by exact_mod_cast hQ
  have hh : density T ≤ (129 : ℝ)^(2*C.card)*density H := by
    unfold density
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right hHr hN.le
  have hq : 1 ≤ (65 : ℝ)^(2*C.card)*density Q := by
    unfold density
    rw [← mul_div_assoc,le_div_iff₀ hN,one_mul]
    exact hQr
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (8385 : ℝ)^(2*C.card))).mpr
  have hp := mul_le_mul hh hq (by norm_num) (mul_nonneg (by positivity) (density_nonneg H))
  rw [mul_one] at hp
  calc
    _ ≤ _ := hp
    _ = _ := by
      rw [show (8385 : ℝ) = 129*65 by norm_num,mul_pow]
      ring

/-- Actual correlation with the integrated local quadratic phase, not merely
a derivative-frequency graph or an averaged antisymmetry bound. The original
local frequency-map domain and all rank/cardinality costs remain explicit. -/
theorem large_U3_local_quadratic_correlation
    (h2 : Function.Bijective (fun x : G ↦ x+x))
    (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hU : δ ≤ uniformityPower 2 f) :
    ∃ B E : Finset (AddChar G ℂ), ∃ F : G → AddChar G ℂ,
    ∃ T : Finset G, ∃ a : G, ∃ χ : AddChar G ℂ,
      0 ∈ T ∧ T ⊆ bohr B (1/16) ∧
      δ^5/256*(Fintype.card G : ℝ) ≤
        extractionLoss δ*(129 : ℝ)^(2*B.card)*(T.card : ℝ) ∧
      (B.card : ℝ) ≤ rankBound δ ∧ F 0 = 0 ∧
      LocallyAdditive (bohr B (1/2) : Set G) F ∧
      (E.card : ℝ) ≤ symmetryRank (density T) ((δ/2)^8*(density T)^4) (δ/16) ∧
      bohr E (1/2) ⊆ bohr B (1/4) ∧
      δ*density T/(8*(8385 : ℝ)^(2*(B ∪ E).card)) ≤
        ‖𝔼 y, if y ∈ doubledBohr (B ∪ E) (1/8) then
          f (a+y)*conj (Erdos3LocalQuadraticIntegration.quadraticPhase F (halfHom h2) y)*conj (χ y)
          else 0‖^2 := by
  have hδ1 : δ ≤ 1 := hU.trans (uniformityPower_le_one 2 f hf)
  obtain ⟨B,E,F,T,a₀,χ₀,hT0,hTsub,hsize,hB,hF0,hadd,hdiff,hcoef,hE,hEsub,hsym⟩ :=
    large_U3_approximate_symmetry f hf hδ hU (by positivity : 0 < δ/16)
  let C := B ∪ E
  let Q := doubledBohr C (1/16)
  let R := doubledBohr C (1/8)
  have hQ : Q.Nonempty := doubledBohr_nonempty C (by norm_num)
  obtain ⟨H,t₀,hH0,hHsub,hHsize,ht₀,hHT⟩ := exists_doubled_bohr_restriction h2 C T ⟨0,hT0⟩
  have hH : H.Nonempty := ⟨0,hH0⟩
  have hR : Q+H ⊆ R := by
    intro x hx
    obtain ⟨y,hy,h,hh,rfl⟩ := mem_add.mp hx
    simpa only [show (1/16 : ℝ)+1/16 = 1/8 by norm_num] using doubledBohr_add C hy (hHsub hh)
  let q : G → ℂ := Erdos3LocalQuadraticIntegration.quadraticPhase F (halfHom h2)
  let u : G → ℂ := fun x ↦ f (x+(a₀+t₀))
  let v : G → ℂ := fun x ↦ f x*(F t₀+χ₀) x
  have hu (x : G) : ‖u x‖ ≤ 1 := hf _
  have hv (x : G) : ‖v x‖ ≤ 1 := by
    simpa only [v,norm_mul,AddChar.norm_apply,mul_one] using hf x
  have hq (x : G) : ‖q x‖ = 1 := quadraticPhase_norm F (halfHom h2) x
  have hc (h : G) (hh : h ∈ H) : δ/2 ≤ ‖mixedCoefficient u v F h‖^2 := by
    rw [shifted_mixed_coefficient]
    have hhF : F h = F (h+t₀)-F t₀ := by
      simpa only [add_sub_cancel_right] using hdiff (h+t₀) (hHT h hh) t₀ ht₀
    rw [hhF,show F (h+t₀)-F t₀+(F t₀+χ₀) = F (h+t₀)+χ₀ by abel,
      show h+(a₀+t₀) = (h+t₀)+a₀ by abel]
    exact hcoef (h+t₀) (hHT h hh)
  have hmean : δ/2 ≤ 𝔼 h : H, ‖mixedCoefficient u v F h‖^2 := by
    letI : Nonempty H := hH.to_subtype
    exact le_expect univ_nonempty (fun h _ ↦ hc h h.property)
  have happrox (h : G) (hh : h ∈ H) (x : G) (hx : x ∈ Q) :
      ‖derivative q h x-q h*F h x‖ ≤ δ/8 := by
    have hxhalf : halfHom h2 x ∈ bohr C (1/8) := bohr_mono C (by norm_num : (1/16 : ℝ) ≤ 1/8)
      ((mem_doubledBohr h2 C (1/16) x).mp hx)
    have hhhalf : halfHom h2 h ∈ bohr C (1/8) := bohr_mono C (by norm_num : (1/16 : ℝ) ≤ 1/8)
      ((mem_doubledBohr h2 C (1/16) h).mp (hHsub hh))
    have hp := integrated_derivative_on_refined_bohr B E F hadd (halfHom h2)
      (halfHom_double h2) hsym hxhalf hhhalf
    simpa only [double_halfHom,show 2*(δ/16) = δ/8 by ring] using hp
  have hecost : 4*(δ/8)^2 ≤ δ/2 := by nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hδ1)]
  obtain ⟨z,χ,hcorr⟩ := localized_phase_correlation H Q R hH hQ hR u v q F hu hv hq
    (by positivity : 0 ≤ δ/8) hecost hmean happrox
  have hprod : density T/(8385 : ℝ)^(2*C.card) ≤ density H*density Q :=
    density_product_from_card C T H Q hHsize (doubled_small_card h2 C)
  have hlower : δ*density T/(8*(8385 : ℝ)^(2*C.card)) ≤ (δ/2/4)*density H*density Q := by
    have hh := mul_le_mul_of_nonneg_left hprod (show 0 ≤ δ/8 by positivity)
    convert hh using 1 <;> ring
  refine ⟨B,E,F,T,z+(a₀+t₀),χ,hT0,hTsub,hsize,hB,hF0,hadd,hE,hEsub,?_⟩
  apply hlower.trans
  convert hcorr using 1
  congr 2
  apply expect_congr rfl
  intro y _
  change (if y ∈ R then f (z+(a₀+t₀)+y)*conj (q y)*conj (χ y) else 0) =
    (if y ∈ R then u (z+y)*conj (q y)*conj (χ y) else 0)
  by_cases hy : y ∈ R
  · simp only [if_pos hy,u]
    congr 3
    abel
  · simp only [if_neg hy]

#print axioms large_U3_local_quadratic_correlation
end Erdos3U3LocalQuadraticCorrelation
