import Submission.MixedCorrelationFourier

/-! Localizing the base variable, detwisting by an approximately integrated
phase, and applying mixed Fourier energy gives genuine local phase correlation. -/
namespace Erdos3LocalizedQuadraticCorrelation
open Finset Erdos3FiniteFourier Erdos3FiniteUniformity Erdos3TwistedCorrelationEnergy
  Erdos3LinearFormsUniformity Erdos3MixedCorrelationFourier Erdos3CorrelationSifting
open scoped BigOperators Classical Pointwise ComplexConjugate
set_option maxHeartbeats 5000000

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

noncomputable def localizedMixed (Q : Finset G) (u v : G → ℂ)
    (F : G → AddChar G ℂ) (z h : G) : ℂ :=
  𝔼 x : Q, u (z+(x : G)+h)*conj (v (z+x))*conj (F h x)

lemma localizedMixed_mean (Q : Finset G) (hQ : Q.Nonempty) (u v : G → ℂ)
    (F : G → AddChar G ℂ) (h : G) :
    (𝔼 z, conj (F h z)*localizedMixed Q u v F z h) = mixedCoefficient u v F h := by
  letI : Nonempty Q := hQ.to_subtype
  unfold localizedMixed
  simp only [mul_expect]
  rw [expect_comm]
  have he (x : Q) : (𝔼 z, conj (F h z)*(u (z+(x : G)+h)*conj (v (z+x))*conj (F h x))) =
      mixedCoefficient u v F h := by
    calc
      _ = 𝔼 z, u (z+(x : G)+h)*conj (v (z+x))*conj (F h (z+x)) := by
        apply expect_congr rfl
        intro z _
        rw [AddChar.map_add_eq_mul,map_mul]
        ring
      _ = _ := Fintype.expect_equiv (Equiv.addRight (x : G)) _ _ (fun _ ↦ rfl)
  simp only [he,Fintype.expect_const]

/-- Base-variable localization preserves the averaged squared mixed correlation;
the character's dependence on the center is kept as a unit scalar. -/
theorem exists_localized_mixed_mean (H Q : Finset G) (hQ : Q.Nonempty)
    (u v : G → ℂ) (F : G → AddChar G ℂ) {κ : ℝ}
    (hc : κ ≤ 𝔼 h : H, ‖mixedCoefficient u v F h‖^2) :
    ∃ z : G, κ ≤ 𝔼 h : H, ‖localizedMixed Q u v F z h‖^2 := by
  have hh (h : G) : ‖mixedCoefficient u v F h‖^2 ≤ 𝔼 z, ‖localizedMixed Q u v F z h‖^2 := by
    rw [← localizedMixed_mean Q hQ u v F h]
    exact mean_product_sq_le _ _ (fun z ↦ by simp only [Complex.norm_conj,AddChar.norm_apply,le_refl])
  have hmean := hc.trans (expect_le_expect (fun h _ ↦ hh h))
  rw [expect_comm] at hmean
  obtain ⟨z,_,hz⟩ := exists_max_image univ (fun z ↦ 𝔼 h : H, ‖localizedMixed Q u v F z h‖^2) univ_nonempty
  exact ⟨z,hmean.trans (expect_le univ_nonempty hz)⟩

lemma unit_detwist_error (a d z : ℂ) (hz : ‖z‖ = 1) :
    ‖conj a-z*conj d‖ = ‖d-z*a‖ := by
  have he : conj a-z*conj d = z*conj (z*a-d) := by
    simp only [map_sub,map_mul]
    calc
      _ = (z*conj z)*conj a-z*conj d := by rw [mul_conj_eq_one hz,one_mul]
      _ = _ := by ring
  rw [he,norm_mul,hz,one_mul,Complex.norm_conj,norm_sub_rev]

lemma localized_detwist_error (H Q R : Finset G) (hQ : Q.Nonempty) (hR : Q+H ⊆ R)
    (u v q : G → ℂ) (F : G → AddChar G ℂ)
    (hu : ∀ x, ‖u x‖ ≤ 1) (hv : ∀ x, ‖v x‖ ≤ 1) (hq : ∀ x, ‖q x‖ = 1)
    {e : ℝ} (happrox : ∀ h ∈ H, ∀ x ∈ Q, ‖derivative q h x-q h*F h x‖ ≤ e)
    (z : G) {h : G} (hh : h ∈ H) :
    ‖localizedMixed Q u v F z h-q h*(𝔼 x : Q,
      (if (x : G)+h ∈ R then u (z+((x : G)+h))*conj (q ((x : G)+h)) else 0)*
        conj (v (z+x)*conj (q x)))‖ ≤ e := by
  letI : Nonempty Q := hQ.to_subtype
  unfold localizedMixed
  rw [mul_expect,← expect_sub_distrib]
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply expect_le univ_nonempty
  intro x _
  rw [if_pos (hR (add_mem_add x.property hh))]
  have he : u (z+(x : G)+h)*conj (v (z+x))*conj (F h x)-
      q h*(u (z+((x : G)+h))*conj (q ((x : G)+h))*conj (v (z+x)*conj (q x))) =
      (u (z+(x : G)+h)*conj (v (z+x)))*(conj (F h x)-q h*conj (derivative q h x)) := by
    simp only [derivative,map_mul,starRingEnd_self_apply,add_assoc]
    ring
  rw [he,norm_mul,unit_detwist_error _ _ _ (hq h)]
  have hp : ‖u (z+(x : G)+h)*conj (v (z+x))‖ ≤ 1 := by
    rw [norm_mul,Complex.norm_conj]
    exact (mul_le_mul (hu _) (hv _) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  exact ((mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans_eq (one_mul _)).trans
    (happrox h hh x x.property)

/-- Approximate local integration and substantial compatible mixed correlations
force actual correlation with q times a linear character on any specified R containing Q+H.
The function q is only required to integrate on the indicated local pairs. -/
theorem localized_phase_correlation (H Q R : Finset G) (hH : H.Nonempty) (hQ : Q.Nonempty)
    (hR : Q+H ⊆ R)
    (u v q : G → ℂ) (F : G → AddChar G ℂ)
    (hu : ∀ x, ‖u x‖ ≤ 1) (hv : ∀ x, ‖v x‖ ≤ 1) (hq : ∀ x, ‖q x‖ = 1)
    {κ e : ℝ} (he : 0 ≤ e) (hecost : 4*e^2 ≤ κ)
    (hc : κ ≤ 𝔼 h : H, ‖mixedCoefficient u v F h‖^2)
    (happrox : ∀ h ∈ H, ∀ x ∈ Q, ‖derivative q h x-q h*F h x‖ ≤ e) :
    ∃ z : G, ∃ χ : AddChar G ℂ,
      (κ/4)*density H*density Q ≤
        ‖𝔼 y, if y ∈ R then u (z+y)*conj (q y)*conj (χ y) else 0‖^2 := by
  letI : Nonempty H := hH.to_subtype
  obtain ⟨z,hz⟩ := exists_localized_mixed_mean H Q hQ u v F hc
  let a : G → ℂ := fun y ↦ if y ∈ R then u (z+y)*conj (q y) else 0
  let b : G → ℂ := fun x ↦ v (z+x)*conj (q x)
  let r : G → ℂ := fun h ↦ 𝔼 x : Q, a ((x : G)+h)*conj (b x)
  have hb (x : G) : ‖b x‖ ≤ 1 := by
    simpa only [b,norm_mul,Complex.norm_conj,hq,mul_one] using hv (z+x)
  have herr (h : H) : ‖localizedMixed Q u v F z h-q h*r h‖ ≤ e :=
    localized_detwist_error H Q R hQ hR u v q F hu hv hq happrox z h.property
  have hsq (h : H) : ‖localizedMixed Q u v F z h‖^2 ≤ 2*‖r h‖^2+2*e^2 := by
    have hn : ‖localizedMixed Q u v F z h‖ ≤ e+‖r h‖ := by
      calc
        _ = ‖(localizedMixed Q u v F z h-q h*r h)+q h*r h‖ := by congr 1; ring
        _ ≤ ‖localizedMixed Q u v F z h-q h*r h‖+‖q h*r h‖ := norm_add_le _ _
        _ ≤ _ := by simpa only [norm_mul,hq,one_mul] using add_le_add (herr h) (le_refl ‖q h*r h‖)
    have hp := pow_le_pow_left₀ (norm_nonneg _) hn 2
    nlinarith [sq_nonneg (e-‖r h‖)]
  have hmean : κ/4 ≤ 𝔼 h : H, ‖r h‖^2 := by
    have hh := hz.trans (expect_le_expect (fun h _ ↦ hsq h))
    rw [expect_add_distrib,← mul_expect,Fintype.expect_const] at hh
    linarith
  obtain ⟨χ,hχ⟩ := localized_mixed_inverse H Q hH hQ a b hb hmean
  refine ⟨z,χ,?_⟩
  convert hχ using 1
  congr 2
  apply expect_congr rfl
  intro y _
  by_cases hy : y ∈ R <;> simp [a,hy]

#print axioms localized_phase_correlation
end Erdos3LocalizedQuadraticCorrelation
