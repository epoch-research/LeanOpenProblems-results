import Submission.StableMaskedUniformity
import Submission.UniformFactorDistribution

/-! A local quadratic counting theorem on stable Bohr windows. Character
uniformity is measured on zero extensions in the ambient finite field; the
quadratic identity is required only on configurations inside the window.
Both density losses and the discarded boundary are explicit. -/
namespace Erdos3LocalQuadraticDistribution
open Finset Erdos3StableMaskedUniformity Erdos3UniformFactorDistribution
  Erdos3BohrPatternGeometry Erdos3FiniteUniformity Erdos3CorrelationSifting
  Erdos3RelativeStableBohr Erdos3FiniteBohr Erdos3StableWindowCounting
  Erdos3QuadraticModelTransfer Erdos3QuadraticModelCounting
open scoped BigOperators Classical
set_option maxHeartbeats 6000000

variable {F G : Type*} [Field F] [Fintype F] [AddCommGroup G] [Fintype G]

lemma independent_triple_expect (χ₀ χ₁ χ₂ : AddChar G ℂ) :
    (𝔼 y : Fin 3 → G, ∏ i : Fin 3, (![χ₀,χ₁,χ₂] i) (y i)) =
      (𝔼 p : G × G × G, χ₀ p.1*χ₁ p.2.1*χ₂ p.2.2) := by
  have he : (𝔼 y : Fin 3 → G, ∏ i : Fin 3, (![χ₀,χ₁,χ₂] i) (y i)) =
      ∏ i : Fin 3, 𝔼 y : G, (![χ₀,χ₁,χ₂] i) y := by
    simp only [Fintype.expect_eq_sum_div_card,Fintype.card_pi,← Fintype.prod_sum,
      Nat.cast_prod,prod_div_distrib]
  rw [he]
  simp only [Fin.prod_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,expect_triple,← expect_mul,← mul_expect]
  rfl

/-- The local triple-distribution hypothesis follows from the ambient masked
U2 bounds. Unlike global orthogonality, this keeps the two density costs. -/
theorem local_triple_discrepancy (B : Finset F) (hB : B.Nonempty)
    (v : Fin 3 → F) (hv : Function.Injective v) (hv₀ : v 0 = 0)
    (C : Finset (AddChar F ℂ)) {r : ℝ} (hr : 0 < r)
    {z : ℕ} (hz : 0 < z) (hstable : RelativeStable C z r)
    (hs : ∀ b c : B, ∀ i, v i*((c : F)-b) ∈ bohr C (relativeWidth C z r))
    (q : F → G) {η : ℝ} (hη : 0 ≤ η)
    (hU : ∀ χ : AddChar G ℂ, χ ≠ 1 →
      uniformityPower 1 (mask (bohr C r) (fun x ↦ χ (q x))) ≤ η^4)
    (χ₀ χ₁ χ₂ : AddChar G ℂ) :
    ‖(𝔼 b : B, 𝔼 c : B, 𝔼 t : bohr C r,
      χ₀ (q (t+v 0*((c : F)-b)))*χ₁ (q (t+v 1*((c : F)-b)))*
        χ₂ (q (t+v 2*((c : F)-b))))-
      (𝔼 p : G × G × G, χ₀ p.1*χ₁ p.2.1*χ₂ p.2.2)‖ ≤
      η/(density (bohr C r)*density B)+3/(z : ℝ) := by
  letI : Nonempty B := hB.to_subtype
  letI : Nonempty (bohr C r) := ⟨⟨0,bohr_zero C hr.le⟩⟩
  let χ : Fin 3 → AddChar G ℂ := ![χ₀,χ₁,χ₂]
  by_cases hall : ∀ i, χ i = 1
  · have h0 := hall 0
    have h1 := hall 1
    have h2 := hall 2
    change χ₀ = 1 at h0
    change χ₁ = 1 at h1
    change χ₂ = 1 at h2
    simp only [h0,h1,h2,AddChar.one_apply,one_mul,Fintype.expect_const,sub_self,norm_zero]
    exact add_nonneg (div_nonneg hη (mul_nonneg (density_nonneg _) (density_nonneg _))) (by positivity)
  · push_neg at hall
    obtain ⟨i,hi⟩ := hall
    have hzmean : (𝔼 p : G × G × G, χ₀ p.1*χ₁ p.2.1*χ₂ p.2.2) = 0 := by
      rw [← independent_triple_expect]
      exact independent_characters_zero χ i hi
    rw [hzmean,sub_zero]
    have h : ‖localDifferenceAverage (bohr C r) B v (fun j x ↦ χ j (q x))‖ ≤
        η/(density (bohr C r)*density B)+3/(z : ℝ) :=
      stable_window_uniformity_bound 0 B hB v hv 0 hv₀ C hr hz hstable hs
        (fun j x ↦ χ j (q x)) (fun j x ↦ ((χ j).norm_apply _).le) i hη (by simpa using hU (χ i) hi)
    simpa only [localDifferenceAverage,show 0+3 = 3 from rfl,Fin.prod_univ_three,χ,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] using h

variable {D : Type*} [Fintype D] [Nonempty D]

/-- A boundary-tolerant transfer to the positive pure-quadratic model. The
fourth value is forced by the relation only on interior configurations. -/
theorem local_quadratic_model_lower
    (C : Finset (AddChar F ℂ)) {r : ℝ} (hr : 0 < r)
    {z : ℕ} (hz : 0 < z) (hstable : RelativeStable C z r)
    (s : D → Fin 4 → F) (hs : ∀ d i, s d i ∈ bohr C (relativeWidth C z r))
    (q : F → G) (Φ : G → ℝ) (hΦ : ∀ y, 0 ≤ Φ y ∧ Φ y ≤ 1)
    (hrel : ∀ d (t : bohr C r), (∀ i : Fin 4, (t : F)+s d i ∈ bohr C r) →
      q ((t : F)+s d 3) = q ((t : F)+s d 0)-3 • q ((t : F)+s d 1)+3 • q ((t : F)+s d 2))
    {ε : ℝ} (hε : 0 ≤ ε)
    (hdisc : ∀ χ₀ χ₁ χ₂ : AddChar G ℂ,
      ‖(𝔼 d : D, 𝔼 t : bohr C r,
        χ₀ (q ((t : F)+s d 0))*χ₁ (q ((t : F)+s d 1))*χ₂ (q ((t : F)+s d 2)))-
        (𝔼 p : G × G × G, χ₀ p.1*χ₁ p.2.1*χ₂ p.2.2)‖ ≤ ε) :
    (𝔼 y : G, Φ y)^4-ε*(Fintype.card G : ℝ)^2-4/(z : ℝ) ≤
      windowPatternAverage (bohr C r) s (fun t ↦ Φ (q t)) := by
  let a (i : Fin 4) (p : D × bohr C r) := q ((p.2 : F)+s p.1 i)
  let forced (p : D × bohr C r) := a 0 p-3 • a 1 p+3 • a 2 p
  let L (d : D) (t : bohr C r) :=
    Φ (a 0 (d,t))*Φ (a 1 (d,t))*Φ (a 2 (d,t))*Φ (forced (d,t))
  have hmodel := quadratic_model_lower_bounded Φ
    (fun y ↦ by rw [abs_of_nonneg (hΦ y).1]; exact (hΦ y).2)
    (a 0) (a 1) (a 2) forced (fun _ ↦ rfl) hε (fun χ₀ χ₁ χ₂ ↦ by
      rw [show (𝔼 p : D × bohr C r, χ₀ (a 0 p)*χ₁ (a 1 p)*χ₂ (a 2 p)) =
          𝔼 d : D, 𝔼 t : bohr C r, χ₀ (a 0 (d,t))*χ₁ (a 1 (d,t))*χ₂ (a 2 (d,t))
        from expect_product _ _ _]
      exact hdisc χ₀ χ₁ χ₂)
  have hmodel' : (𝔼 y : G, Φ y)^4-ε*(Fintype.card G : ℝ)^2 ≤ 𝔼 d : D, 𝔼 t : bohr C r, L d t := by
    exact hmodel.trans_eq (expect_product (univ : Finset D) (univ : Finset (bohr C r))
      (fun p : D × bohr C r ↦ L p.1 p.2))
  have hpoint (d : D) (t : bohr C r) :
      L d t-(∏ i : Fin 4, Φ (q ((t : F)+s d i))) ≤
        1-interiorMask (bohr C r) (s d) t := by
    by_cases hin : ∀ i : Fin 4, (t : F)+s d i ∈ bohr C r
    · rw [(interiorMask_eq_one_iff _ _ _).mpr hin]
      dsimp [L,forced,a]
      rw [← hrel d t hin,Fin.prod_univ_four]
      simp
    · have hm : interiorMask (bohr C r) (s d) t = 0 := by
        simp only [interiorMask,indicator,Fintype.prod_boole,if_neg hin]
      rw [hm,sub_zero]
      have hL : L d t ≤ 1 := by
        dsimp [L]
        exact mul_le_one₀ (mul_le_one₀ (mul_le_one₀ (hΦ _).2 (hΦ _).1 (hΦ _).2)
          (hΦ _).1 (hΦ _).2) (hΦ _).1 (hΦ _).2
      have hR : 0 ≤ ∏ i : Fin 4, Φ (q ((t : F)+s d i)) := prod_nonneg (fun i _ ↦ (hΦ _).1)
      linarith
  have herr : (𝔼 d : D, 𝔼 t : bohr C r, L d t)-
      windowPatternAverage (bohr C r) s (fun t ↦ Φ (q t)) ≤ 4/(z : ℝ) := by
    unfold windowPatternAverage
    rw [← expect_sub_distrib]
    apply expect_le univ_nonempty
    intro d _
    rw [← expect_sub_distrib]
    apply (expect_le_expect (fun t _ ↦ hpoint d t)).trans
    simpa only [Fintype.card_fin] using boundary_mass_le C hr hz hstable (s d) (hs d)
  linarith

/-- An actual local count lower bound with no joint-discrepancy hypothesis:
only the masked single-character uniformity and local quadraticity remain. -/
theorem local_count_of_masked_U2 (B : Finset F) (hB : B.Nonempty)
    (v : Fin 4 → F) (hv : Function.Injective v) (hv₀ : v 0 = 0)
    (C : Finset (AddChar F ℂ)) {r : ℝ} (hr : 0 < r)
    {z : ℕ} (hz : 0 < z) (hstable : RelativeStable C z r)
    (hs : ∀ b c : B, ∀ i, v i*((c : F)-b) ∈ bohr C (relativeWidth C z r))
    (q : F → G) (Φ : G → ℝ) (hΦ : ∀ y, 0 ≤ Φ y ∧ Φ y ≤ 1)
    (hrel : ∀ b c : B, ∀ t : bohr C r,
      (∀ i : Fin 4, (t : F)+v i*((c : F)-b) ∈ bohr C r) →
      q ((t : F)+v 3*((c : F)-b)) =
        q ((t : F)+v 0*((c : F)-b))-3 • q ((t : F)+v 1*((c : F)-b))+
          3 • q ((t : F)+v 2*((c : F)-b)))
    {η : ℝ} (hη : 0 ≤ η)
    (hU : ∀ χ : AddChar G ℂ, χ ≠ 1 →
      uniformityPower 1 (mask (bohr C r) (fun x ↦ χ (q x))) ≤ η^4) :
    (𝔼 y : G, Φ y)^4-
        (η/(density (bohr C r)*density B)+3/(z : ℝ))*(Fintype.card G : ℝ)^2-
        4/(z : ℝ) ≤
      windowPatternAverage (bohr C r)
        (fun (p : B × B) i ↦ v i*((p.2 : F)-p.1)) (fun t ↦ Φ (q t)) := by
  letI : Nonempty B := hB.to_subtype
  apply local_quadratic_model_lower C hr hz hstable
    (fun (p : B × B) i ↦ v i*((p.2 : F)-p.1)) (fun p i ↦ hs p.1 p.2 i)
    q Φ hΦ (fun p t ↦ hrel p.1 p.2 t) ?_ ?_
  · exact add_nonneg (div_nonneg hη (mul_nonneg (density_nonneg _) (density_nonneg _))) (by positivity)
  · intro χ₀ χ₁ χ₂
    have h := local_triple_discrepancy B hB (fun i : Fin 3 ↦ v i.castSucc)
      (hv.comp (Fin.castSucc_injective 3)) hv₀ C hr hz hstable
      (fun b c i ↦ hs b c i.castSucc) q hη hU χ₀ χ₁ χ₂
    have he := expect_product (univ : Finset B) (univ : Finset B)
      (fun p : B × B ↦ 𝔼 t : bohr C r,
        χ₀ (q ((t : F)+v 0*((p.2 : F)-p.1)))*
        χ₁ (q ((t : F)+v 1*((p.2 : F)-p.1)))*
        χ₂ (q ((t : F)+v 2*((p.2 : F)-p.1))))
    simp only [univ_product_univ] at he
    rw [he]
    exact h

#print axioms local_count_of_masked_U2

#print axioms local_triple_discrepancy
#print axioms local_quadratic_model_lower
end Erdos3LocalQuadraticDistribution
