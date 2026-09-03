import Submission.BoundedFrequencyPhaseApproximation

/-! Local counting with bounded-frequency distribution tests only. All support,
boundary, and observable-defect conditions are explicit. -/
namespace Erdos3LocalFrequencyModel
open Finset Erdos3SparseFourierModelTransfer Erdos3LocalQuadraticDistribution
  Erdos3FiniteFrequencyCoordinates Erdos3StableMaskedUniformity
  Erdos3FiniteUniformity Erdos3CorrelationSifting Erdos3RelativeStableBohr
  Erdos3FiniteBohr Erdos3StableWindowCounting Erdos3BohrPatternGeometry
  Erdos3UniformFactorDistribution Erdos3FiniteFourier Erdos3FourierMultilinearTransfer
open scoped BigOperators Classical
set_option maxHeartbeats 7000000
variable {F I : Type*} [Field F] [Fintype F] [Fintype I] [DecidableEq I]
  {N : ℕ} [NeZero N]

theorem local_triple_discrepancy_frequency (B : Finset F) (hB : B.Nonempty)
    (v : Fin 3 → F) (hv : Function.Injective v) (hv₀ : v 0 = 0)
    (C : Finset (AddChar F ℂ)) {r : ℝ} (hr : 0 < r)
    {z : ℕ} (hz : 0 < z) (hstable : RelativeStable C z r)
    (hs : ∀ b c : B, ∀ i, v i*((c : F)-b) ∈ bohr C (relativeWidth C z r))
    (R : ℕ) (q : F → I → ZMod N) {η : ℝ} (hη : 0 ≤ η)
    (hU : ∀ χ : AddChar (I → ZMod N) ℂ, HasFrequencyBound R χ → χ ≠ 1 →
      uniformityPower 1 (mask (bohr C r) (fun x ↦ χ (q x))) ≤ η^4)
    (χ₀ χ₁ χ₂ : AddChar (I → ZMod N) ℂ)
    (hχ₀ : HasFrequencyBound R χ₀) (hχ₁ : HasFrequencyBound R χ₁)
    (hχ₂ : HasFrequencyBound R χ₂) :
    ‖(𝔼 b : B, 𝔼 c : B, 𝔼 t : bohr C r,
      χ₀ (q (t+v 0*((c : F)-b)))*χ₁ (q (t+v 1*((c : F)-b)))*
        χ₂ (q (t+v 2*((c : F)-b))))-
      (𝔼 p : (I → ZMod N) × (I → ZMod N) × (I → ZMod N), χ₀ p.1*χ₁ p.2.1*χ₂ p.2.2)‖ ≤
      η/(density (bohr C r)*density B)+3/(z : ℝ) := by
  letI : Nonempty B := hB.to_subtype
  letI : Nonempty (bohr C r) := ⟨⟨0,bohr_zero C hr.le⟩⟩
  let χ : Fin 3 → AddChar (I → ZMod N) ℂ := ![χ₀,χ₁,χ₂]
  have hχ (j : Fin 3) : HasFrequencyBound R (χ j) := by fin_cases j <;> assumption
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
    have hzmean : (𝔼 p : (I → ZMod N) × (I → ZMod N) × (I → ZMod N), χ₀ p.1*χ₁ p.2.1*χ₂ p.2.2) = 0 := by
      rw [← independent_triple_expect]
      exact independent_characters_zero χ i hi
    rw [hzmean,sub_zero]
    have h : ‖localDifferenceAverage (bohr C r) B v (fun j x ↦ χ j (q x))‖ ≤
        η/(density (bohr C r)*density B)+3/(z : ℝ) :=
      stable_window_uniformity_bound 0 B hB v hv 0 hv₀ C hr hz hstable hs
        (fun j x ↦ χ j (q x)) (fun j x ↦ ((χ j).norm_apply _).le) i hη (by simpa using hU (χ i) (hχ i) hi)
    simpa only [localDifferenceAverage,show 0+3 = 3 from rfl,Fin.prod_univ_three,χ,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] using h

variable {D : Type*} [Fintype D] [Nonempty D]

theorem local_frequency_model_lower_of_defect
    (C : Finset (AddChar F ℂ)) {r : ℝ} (hr : 0 < r)
    {z : ℕ} (hz : 0 < z) (hstable : RelativeStable C z r)
    (s : D → Fin 4 → F) (hs : ∀ d i, s d i ∈ bohr C (relativeWidth C z r))
    (R : ℕ) (q : F → I → ZMod N) (Φ : (I → ZMod N) → ℝ) (hΦ : ∀ y, 0 ≤ Φ y ∧ Φ y ≤ 1)
    (hsupport : ∀ χ, ¬ HasFrequencyBound R χ → hat (fun y ↦ (Φ y : ℂ)) χ = 0)
    {ν : ℝ} (hν : 0 ≤ ν)
    (hdef : ∀ d (t : bohr C r), (∀ i : Fin 4, (t : F)+s d i ∈ bohr C r) →
      |Φ (q ((t : F)+s d 3))-
        Φ (q ((t : F)+s d 0)-3 • q ((t : F)+s d 1)+3 • q ((t : F)+s d 2))| ≤ ν)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hdisc : ∀ χ₀ χ₁ χ₂ : AddChar (I → ZMod N) ℂ,
      HasFrequencyBound (4*R) χ₀ → HasFrequencyBound (4*R) χ₁ → HasFrequencyBound (4*R) χ₂ →
      ‖(𝔼 d : D, 𝔼 t : bohr C r,
        χ₀ (q ((t : F)+s d 0))*χ₁ (q ((t : F)+s d 1))*χ₂ (q ((t : F)+s d 2)))-
        (𝔼 p : (I → ZMod N) × (I → ZMod N) × (I → ZMod N), χ₀ p.1*χ₁ p.2.1*χ₂ p.2.2)‖ ≤ ε) :
    (𝔼 y : I → ZMod N, Φ y)^4-ε*fourierMass (fun y ↦ (Φ y : ℂ))^4-ν-4/(z : ℝ) ≤
      windowPatternAverage (bohr C r) s (fun t ↦ Φ (q t)) := by
  letI : Nonempty (bohr C r) := ⟨⟨0,bohr_zero C hr.le⟩⟩
  let a (i : Fin 4) (p : D × bohr C r) := q ((p.2 : F)+s p.1 i)
  let forced (p : D × bohr C r) := a 0 p-3 • a 1 p+3 • a 2 p
  let L (d : D) (t : bohr C r) :=
    Φ (a 0 (d,t))*Φ (a 1 (d,t))*Φ (a 2 (d,t))*Φ (forced (d,t))
  have hmodel := bounded_frequency_model_lower R Φ hsupport
    (a 0) (a 1) (a 2) forced (fun _ ↦ rfl) (fun χ₀ χ₁ χ₂ hχ₀ hχ₁ hχ₂ ↦ by
      rw [show (𝔼 p : D × bohr C r, χ₀ (a 0 p)*χ₁ (a 1 p)*χ₂ (a 2 p)) =
          𝔼 d : D, 𝔼 t : bohr C r, χ₀ (a 0 (d,t))*χ₁ (a 1 (d,t))*χ₂ (a 2 (d,t))
        from expect_product _ _ _]
      exact hdisc χ₀ χ₁ χ₂ hχ₀ hχ₁ hχ₂)
  have hmodel' : (𝔼 y : I → ZMod N, Φ y)^4-ε*fourierMass (fun y ↦ (Φ y : ℂ))^4 ≤ 𝔼 d : D, 𝔼 t : bohr C r, L d t := by
    exact hmodel.trans_eq (expect_product (univ : Finset D) (univ : Finset (bohr C r))
      (fun p : D × bohr C r ↦ L p.1 p.2))
  have hpoint (d : D) (t : bohr C r) :
      L d t-(∏ i : Fin 4, Φ (q ((t : F)+s d i))) ≤
        ν+(1-interiorMask (bohr C r) (s d) t) := by
    by_cases hin : ∀ i : Fin 4, (t : F)+s d i ∈ bohr C r
    · rw [(interiorMask_eq_one_iff _ _ _).mpr hin,sub_self,add_zero]
      let c := Φ (a 0 (d,t))*Φ (a 1 (d,t))*Φ (a 2 (d,t))
      have hc0 : 0 ≤ c := mul_nonneg (mul_nonneg (hΦ _).1 (hΦ _).1) (hΦ _).1
      have hc1 : c ≤ 1 := mul_le_one₀ (mul_le_one₀ (hΦ _).2 (hΦ _).1 (hΦ _).2) (hΦ _).1 (hΦ _).2
      have hd : Φ (forced (d,t))-Φ (a 3 (d,t)) ≤ ν := by
        have h := (abs_le.mp (hdef d t hin)).1
        dsimp only [forced,a]
        linarith
      calc
        _ = c*(Φ (forced (d,t))-Φ (a 3 (d,t))) := by
          rw [Fin.prod_univ_four]
          dsimp only [L,c,a]
          ring
        _ ≤ c*ν := mul_le_mul_of_nonneg_left hd hc0
        _ ≤ 1*ν := mul_le_mul_of_nonneg_right hc1 hν
        _ = ν := one_mul _
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
      windowPatternAverage (bohr C r) s (fun t ↦ Φ (q t)) ≤ ν+4/(z : ℝ) := by
    unfold windowPatternAverage
    rw [← expect_sub_distrib]
    apply expect_le univ_nonempty
    intro d _
    rw [← expect_sub_distrib]
    apply (expect_le_expect (fun t _ ↦ hpoint d t)).trans
    rw [expect_add_distrib,Fintype.expect_const]
    exact add_le_add le_rfl (by
      simpa only [Fintype.card_fin,Nat.cast_ofNat] using boundary_mass_le C hr hz hstable (s d) (hs d))
  linarith

#print axioms local_triple_discrepancy_frequency
#print axioms local_frequency_model_lower_of_defect
end Erdos3LocalFrequencyModel
