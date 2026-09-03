import Submission.LocalQuadraticDistribution
import Submission.FiniteCircleGrid

/-! Robust local model counting: the exact quadratic relation may be replaced
by a small defect after applying the bounded observable. This is essential for
finite quantizations of circle-valued local phases. -/
namespace Erdos3ApproximateLocalQuadraticCounting
open Finset Erdos3LocalQuadraticDistribution Erdos3FiniteCircleGrid
  Erdos3BohrPatternGeometry Erdos3FiniteUniformity Erdos3CorrelationSifting
  Erdos3RelativeStableBohr Erdos3FiniteBohr Erdos3StableWindowCounting
  Erdos3QuadraticModelTransfer Erdos3QuadraticModelCounting
open scoped BigOperators Classical
set_option maxHeartbeats 6000000

variable {F G D : Type*} [Field F] [Fintype F] [AddCommGroup G] [Fintype G]
  [Fintype D] [Nonempty D]

/-- Only observable-level approximate quadraticity is needed, and only on
interior configurations. The defect and boundary costs are additive. -/
theorem local_quadratic_model_lower_of_defect
    (C : Finset (AddChar F ℂ)) {r : ℝ} (hr : 0 < r)
    {z : ℕ} (hz : 0 < z) (hstable : RelativeStable C z r)
    (s : D → Fin 4 → F) (hs : ∀ d i, s d i ∈ bohr C (relativeWidth C z r))
    (q : F → G) (Φ : G → ℝ) (hΦ : ∀ y, 0 ≤ Φ y ∧ Φ y ≤ 1)
    {ν : ℝ} (hν : 0 ≤ ν)
    (hdef : ∀ d (t : bohr C r), (∀ i : Fin 4, (t : F)+s d i ∈ bohr C r) →
      |Φ (q ((t : F)+s d 3))-
        Φ (q ((t : F)+s d 0)-3 • q ((t : F)+s d 1)+3 • q ((t : F)+s d 2))| ≤ ν)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hdisc : ∀ χ₀ χ₁ χ₂ : AddChar G ℂ,
      ‖(𝔼 d : D, 𝔼 t : bohr C r,
        χ₀ (q ((t : F)+s d 0))*χ₁ (q ((t : F)+s d 1))*χ₂ (q ((t : F)+s d 2)))-
        (𝔼 p : G × G × G, χ₀ p.1*χ₁ p.2.1*χ₂ p.2.2)‖ ≤ ε) :
    (𝔼 y : G, Φ y)^4-ε*(Fintype.card G : ℝ)^2-ν-4/(z : ℝ) ≤
      windowPatternAverage (bohr C r) s (fun t ↦ Φ (q t)) := by
  letI : Nonempty (bohr C r) := ⟨⟨0,bohr_zero C hr.le⟩⟩
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

variable {I : Type*} [Fintype I] {N : ℕ} [NeZero N]

noncomputable def gridObservable (H : (I → ℂ) → ℝ) : (I → ZMod N) → ℝ :=
  fun v ↦ H (gridVector v)

lemma gridObservable_error (H : (I → ℂ) → ℝ) {L : NNReal} (hH : LipschitzWith L H)
    (v : I → ℂ) (hv : ∀ i, ‖v i‖ = 1) :
    |gridObservable (N := N) H (fun i ↦ roundPhase N (v i))-H v| ≤ (L : ℝ)*(8/(N : ℝ)) := by
  exact (hH.dist_le_mul _ _).trans
    (mul_le_mul_of_nonneg_left (gridVector_rounding v hv) L.coe_nonneg)

lemma gridObservable_defect (H : (I → ℂ) → ℝ) {L : NNReal} (hH : LipschitzWith L H)
    (v : Fin 4 → I → ℂ) (hv : ∀ j i, ‖v j i‖ = 1)
    (hrel : ∀ i, v 3 i = quadraticWord (v 0 i) (v 1 i) (v 2 i)) :
    |gridObservable (N := N) H (fun i ↦ roundPhase N (v 3 i))-
      gridObservable H ((fun i ↦ roundPhase N (v 0 i))-
        3 • (fun i ↦ roundPhase N (v 1 i))+3 • (fun i ↦ roundPhase N (v 2 i)))| ≤
      (L : ℝ)*(64/(N : ℝ)) := by
  exact (hH.dist_le_mul _ _).trans
    (mul_le_mul_of_nonneg_left (gridVector_quadratic_defect v hv hrel) L.coe_nonneg)

#print axioms local_quadratic_model_lower_of_defect
#print axioms gridObservable_defect
end Erdos3ApproximateLocalQuadraticCounting
