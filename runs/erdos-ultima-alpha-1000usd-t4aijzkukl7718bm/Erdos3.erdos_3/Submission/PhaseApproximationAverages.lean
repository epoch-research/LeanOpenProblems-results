import Submission.PolynomialCocycleIntegration
import Submission.DerivativeSpectrum

/-! Quantitative L1 approximation by constants and characters, and elementary
exceptional-mass estimates for near-maximal uniformity arguments. -/
namespace Erdos3PhaseApproximationAverages
open Finset Erdos3PolynomialCocycleIntegration Erdos3DensePolynomialCocycle
  Erdos3PolynomialDerivativeConsistency Erdos3HigherUniformityPerturbation
  Erdos3HigherPolynomialSeparation Erdos3HigherPhaseDifferences
  Erdos3HigherPhaseRepresentation Erdos3HigherLocalPolynomialProgressions
  Erdos3FiniteUniformity Erdos3DerivativeSpectrum Erdos3FiniteFourier
  Erdos3QuadraticRecurrenceAverages Erdos3FiniteSamplingMoments Erdos3LinearFormsUniformity
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 3000000
variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma phase_pair_distance_mean (q : G → Additive Circle) :
    (𝔼 y : G, 𝔼 x : G, ‖phase (q x)-phase (q y)‖^2) = 2*(1-‖phaseMean q‖^2) := by
  have he (x y : G) : ‖phase (q x)-phase (q y)‖^2 =
      2*(1-(phase (q x)*conj (phase (q y))).re) := by
    rw [phase_sub_norm,Complex.norm_sub_one_sq_eq_of_norm_eq_one (phase_norm _),phase_sub]
  simp_rw [he,← mul_expect,expect_sub_distrib,Fintype.expect_const]
  rw [expect_comm,← norm_mean_sq_pair]
  rfl

/-- The approximating constant can be chosen among the values of the phase. -/
theorem constant_phase_approximation (q : G → Additive Circle) :
    ∃ c : Additive Circle, (meanDistance (fun x ↦ phase (q x)) (fun _ ↦ phase c))^2 ≤
      2*(1-‖phaseMean q‖^2) := by
  let F : G → ℝ := fun y ↦ 𝔼 x : G, ‖phase (q x)-phase (q y)‖^2
  obtain ⟨y,hy,hmin⟩ := exists_min_image univ F univ_nonempty
  have hymean : F y ≤ 𝔼 z : G, F z := le_expect univ_nonempty hmin
  have hpair : (𝔼 z : G, F z) = 2*(1-‖phaseMean q‖^2) := phase_pair_distance_mean q
  refine ⟨q y,?_⟩
  exact (expect_even_pow_le (by decide : Even 2) (fun x ↦ ‖phase (q x)-phase (q y)‖)).trans
    (hymean.trans_eq hpair)

noncomputable def characterPhase (χ : AddChar G ℂ) (x : G) : Additive Circle :=
  Additive.ofMul (⟨χ x,mem_sphere_zero_iff_norm.mpr (χ.norm_apply x)⟩ : Circle)

lemma characterPhase_value (χ : AddChar G ℂ) (x : G) : phase (characterPhase χ x) = χ x := rfl

lemma characterPhase_polynomial (n : ℕ) (χ : AddChar G ℂ) :
    IsLocallyPolynomial Set.univ (n+1) (characterPhase χ) :=
  (Erdos3HigherUniformityDefect.uniformity_eq_one_iff_polynomial (n+1) (characterPhase χ)).mp
    (character_uniformity n χ)

lemma phase_distance_sub_right (a b c : Additive Circle) :
    ‖phase a-phase (b+c)‖ = ‖phase (a-b)-phase c‖ := by
  rw [phase_sub_norm,phase_sub_norm]
  congr 2
  abel

/-- A near-maximal U2 phase is L1-close to a character times a constant. -/
theorem character_phase_approximation (q : G → Additive Circle) :
    ∃ χ : AddChar G ℂ, ∃ c : Additive Circle,
      (meanDistance (fun x ↦ phase (q x)) (fun x ↦ phase (characterPhase χ x+c)))^2 ≤
        2*(1-uniformityPower 1 (fun x ↦ phase (q x))) := by
  obtain ⟨χ,hχ⟩ := exists_large_fourier (fun x ↦ phase (q x)) (fun x ↦ (phase_norm _).le)
  let r : G → Additive Circle := fun x ↦ q x-characterPhase χ x
  have hr : phaseMean r = hat (fun x ↦ phase (q x)) χ := by
    unfold phaseMean hat
    apply expect_congr rfl
    intro x _
    exact phase_sub _ _
  obtain ⟨c,hc⟩ := constant_phase_approximation r
  refine ⟨χ,c,?_⟩
  have he : meanDistance (fun x ↦ phase (q x)) (fun x ↦ phase (characterPhase χ x+c)) =
      meanDistance (fun x ↦ phase (r x)) (fun _ ↦ phase c) := by
    unfold meanDistance
    exact expect_congr rfl (fun x _ ↦ phase_distance_sub_right _ _ _)
  rw [he]
  rw [hr] at hc
  linarith only [hc,hχ]

lemma mean_square_of_close_constant (q : G → Additive Circle) (c : Additive Circle) :
    1-2*meanDistance (fun x ↦ phase (q x)) (fun _ ↦ phase c) ≤ ‖phaseMean q‖^2 := by
  have he : ‖phaseMean q-phase c‖ ≤ meanDistance (fun x ↦ phase (q x)) (fun _ ↦ phase c) := by
    have hh := RCLike.norm_expect_le (K := ℂ) (s := univ)
      (f := fun x : G ↦ phase (q x)-phase c)
    simpa only [expect_sub_distrib,Fintype.expect_const,phaseMean,meanDistance] using hh
  have hh := norm_sub_le (phaseMean q) (phaseMean q-phase c)
  rw [sub_sub_cancel,phase_norm] at hh
  have hsq := sq_nonneg (‖phaseMean q‖-1)
  nlinarith only [he,hh,hsq]

section Mass
variable {I : Type*} [Fintype I] [Nonempty I]

noncomputable def badMass (S : Finset I) : ℝ := ((univ \ S).card : ℝ)/(Fintype.card I : ℝ)

lemma badMass_nonneg (S : Finset I) : 0 ≤ badMass S := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma expect_bad_indicator (S : Finset I) :
    (𝔼 i : I, if i ∈ univ \ S then (1 : ℝ) else 0) = badMass S := by
  unfold badMass
  rw [Fintype.expect_eq_sum_div_card]
  congr 1
  rw [← sum_filter]
  simp
  congr 1
  ext i
  simp

lemma mean_defect_badMass (S : Finset I) (v : I → ℝ) (hv : ∀ i, 0 ≤ v i)
    {a : ℝ} (ha : 0 ≤ a) (hgood : ∀ i ∈ S, 1-v i ≤ a) :
    1-(𝔼 i : I, v i) ≤ a+badMass S := by
  have hpoint (i : I) : 1-v i ≤ a+(if i ∈ univ \ S then (1 : ℝ) else 0) := by
    by_cases hi : i ∈ S
    · simpa only [mem_sdiff,mem_univ,hi,not_true_eq_false,and_false,if_false,add_zero] using hgood i hi
    · rw [if_pos (mem_sdiff.mpr ⟨mem_univ _,hi⟩)]
      linarith only [hv i,ha]
  have hh := expect_le_expect (s := univ) (fun i _ ↦ hpoint i)
  simpa only [expect_sub_distrib,expect_add_distrib,Fintype.expect_const,expect_bad_indicator] using hh

lemma high_values_badMass (v : I → ℝ) (hv : ∀ i, v i ≤ 1) {τ δ : ℝ}
    (havg : 1-δ ≤ 𝔼 i : I, v i) :
    τ*badMass (univ.filter (fun i ↦ 1-τ ≤ v i)) ≤ δ := by
  let S := univ.filter (fun i ↦ 1-τ ≤ v i)
  have hpoint (i : I) : τ*(if i ∈ univ \ S then (1 : ℝ) else 0) ≤ 1-v i := by
    by_cases hi : i ∈ S
    · rw [if_neg (by simpa only [mem_sdiff,mem_univ,true_and] using not_not.mpr hi),mul_zero]
      linarith only [hv i]
    · have hbad : v i < 1-τ := by simpa only [S,mem_filter,mem_univ,true_and,not_le] using hi
      rw [if_pos (mem_sdiff.mpr ⟨mem_univ _,hi⟩),mul_one]
      linarith only [hbad]
  have hh := expect_le_expect (s := univ) (fun i _ ↦ hpoint i)
  rw [← mul_expect,expect_bad_indicator,expect_sub_distrib,Fintype.expect_const] at hh
  exact hh.trans (by linarith only [havg])

lemma dense_of_badMass_le_eighth (S : Finset I) (hS : badMass S ≤ 1/8) :
    4*(Fintype.card I-S.card) < Fintype.card I := by
  have hN : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hh := (div_le_iff₀ hN).mp hS
  have hc : (4 : ℝ)*((univ \ S).card : ℝ) < (Fintype.card I : ℝ) := by linarith only [hh,hN]
  have hn : 4*(univ \ S).card < Fintype.card I := by exact_mod_cast hc
  simpa only [card_sdiff_of_subset (subset_univ _),card_univ] using hn

end Mass
#print axioms constant_phase_approximation
#print axioms character_phase_approximation
#print axioms high_values_badMass
end Erdos3PhaseApproximationAverages
