import Submission.AveragedLocalCircleCounting
import Submission.StrongLocalizedCounting

/-! Full counting criterion for a bounded strong decomposition represented by
local circle factors. If no four-term progression exists, the criterion gives
a nontrivial rounded local character with large masked U2 power. This is an
explicit structural alternative, not a proof that it cannot occur. -/
namespace Erdos3StrongLocalCharacterCriterion
open Finset Erdos3AveragedLocalCircleCounting Erdos3StrongLocalizedCounting
  Erdos3LocalCircleFactorCounting Erdos3LocalCircleFactorMean
  Erdos3StableMaskedUniformity Erdos3FiniteUniformity Erdos3CorrelationSifting
  Erdos3RelativeStableBohr Erdos3FiniteBohr Erdos3StableWindowCounting
  Erdos3LocalQuadraticInverse Erdos3LocalFactorMean Erdos3ClippedWeakRegularity
  Erdos3LocalizedPatternCriterion Erdos3UniformityCounting
open scoped BigOperators Classical
set_option maxHeartbeats 7000000

variable {F I : Type*} [Field F] [Fintype F] [Fintype I] {N : ℕ} [NeZero N]

lemma mean_difference_of_L2 (f g : F → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (herr : squaredError f g ≤ ε^2) : |(𝔼 x : F, f x)-(𝔼 x : F, g x)| ≤ ε := by
  rw [← expect_sub_distrib]
  exact (Finset.abs_expect_le _ _).trans (mean_abs_le_of_mean_square _ hε herr)

/-- The original density survives the fine-uniformity, coarse/fine L2, and
local L2 approximation steps, all with their independently prescribed errors. -/
lemma strong_local_mean_lower (A : Finset F) (W : Finset F) (hW : W.Nonempty)
    (g g' : F → ℝ) (h : F → F → ℝ)
    {η ε τ : ℝ} (hη : 0 ≤ η) (hε : 0 ≤ ε) (hτ : 0 ≤ τ)
    (hU : uniformityPower 2 (fun x ↦ ((indicator A x-g' x : ℝ) : ℂ)) ≤ η^8)
    (hclose : squaredError g g' ≤ ε^2)
    (hlocal : ∀ a, (𝔼 t : W, (g (a+t)-h a t)^2) ≤ τ^2) :
    density A-η-ε-τ ≤ 𝔼 a : F, 𝔼 t : W, h a t := by
  have h₁ := (abs_le.mp (mean_difference_of_uniformity 2 (indicator A) g' hη hU)).2
  have h₂ := (abs_le.mp (mean_difference_of_L2 g g' hε hclose)).1
  have h₃ := (abs_le.mp (averaged_local_mean_difference W hW g h hτ hlocal)).2
  rw [expect_indicator] at h₁
  linarith

/-- All local/global approximation and distribution losses are paid before
excluding the exact diagonal contribution density(A)/|B|. -/
theorem exists_fourAP_of_strong_character_uniform
    (A B : Finset F) (hB : B.Nonempty)
    (hv : Function.Injective (fun j : Fin 4 ↦ (j.val : F)))
    (C : Finset (AddChar F ℂ)) {r : ℝ} (hr : 0 < r)
    {z : ℕ} (hz : 0 < z) (hstable : RelativeStable C z r)
    (hs : ∀ b c : B, ∀ j : Fin 4,
      (j.val : F)*((c : F)-b) ∈ bohr C (relativeWidth C z r))
    (g g' : F → ℝ) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hg' : ∀ x, 0 ≤ g' x ∧ g' x ≤ 1)
    (Q : F → I → F → ℂ) (hQ : ∀ a i x, ‖Q a i x‖ = 1)
    (hpoly : ∀ a i, IsLocallyQuadratic (bohr C r : Set F) (Q a i))
    (H : F → (I → ℂ) → ℝ) (hH : ∀ a v, 0 ≤ H a v ∧ H a v ≤ 1)
    {L : NNReal} (hLip : ∀ a, LipschitzWith L (H a))
    {θ α η ε τ κ : ℝ} (hθ : 0 ≤ θ) (hα : 0 ≤ α)
    (hη : 0 ≤ η) (hε : 0 ≤ ε) (hτ : 0 ≤ τ) (hκ : 0 ≤ κ)
    (hU : uniformityPower 2 (fun x ↦ ((indicator A x-g' x : ℝ) : ℂ)) ≤ η^8)
    (hclose : squaredError g g' ≤ ε^2)
    (hlocal : ∀ a, (𝔼 t : bohr C r, (g (a+t)-H a (fun i ↦ Q a i t))^2) ≤ τ^2)
    (hboundary : τ^2+1/(z : ℝ) ≤ κ^2)
    (hchar : ∀ a, ∀ χ : AddChar (I → ZMod N) ℂ, χ ≠ 1 →
      uniformityPower 1 (mask (bohr C r) (fun x ↦ χ (roundedFactor (Q a) x))) ≤ θ^4)
    (hmean : α+modelMeanError N (Fintype.card I) L θ (density (bohr C r)) ≤ density A-η-ε-τ)
    (hnum : modelCountError N (Fintype.card I) z L θ (density (bohr C r)) (density B)+
      4*(η/density B+ε+κ)+density A/(B.card : ℝ) < α^4) :
    ∃ x d : F, d ≠ 0 ∧ ∀ j : Fin 4, x+(j.val : F)*d ∈ A := by
  have hmean' := strong_local_mean_lower A (bohr C r) ⟨0,bohr_zero C hr.le⟩
    g g' (fun a t ↦ H a (fun i ↦ Q a i t)) hη hε hτ hU hclose hlocal
  have hcount := averaged_circle_count B hB hv C hr hz hstable hs Q hQ hpoly H hH hLip
    hθ hα hchar (hmean.trans hmean')
  have hbridge := strong_localized_counting_bridge 1 B hB (fun j : Fin 4 ↦ (j.val : F)) hv
    C hr hz hstable hs (indicator A) g g' (fun a t ↦ H a (fun i ↦ Q a i t))
    (indicator_norm_bounds A) hg hg' (fun a t ↦ hH a _) hη hε hκ hU hclose hlocal hboundary
  simp only [show 1+3 = 4 from rfl,Nat.cast_ofNat] at hbridge
  by_contra! hno
  have hdiag : ∀ x d : F, (∀ j : Fin 4, x+(j.val : F)*d ∈ A) → d = 0 := by
    intro x d hm
    by_contra hd
    obtain ⟨j,hj⟩ := hno x d hd
    exact hj (hm j)
  rw [difference_diagonal_average (by decide : 0 < 4) B hB
    (fun j : Fin 4 ↦ (j.val : F)) A hdiag] at hbridge
  linarith [(abs_le.mp hbridge).1]

/-- Under the explicit size/error budgets, a progression-free set forces a
failure of masked lower-order uniformity in one of its local factor characters.
Ruling out or exploiting this alternative is a separate mathematical task. -/
theorem fourAP_free_has_bad_local_character
    (A B : Finset F) (hB : B.Nonempty)
    (hv : Function.Injective (fun j : Fin 4 ↦ (j.val : F)))
    (hfree : ∀ x d : F, (∀ j : Fin 4, x+(j.val : F)*d ∈ A) → d = 0)
    (C : Finset (AddChar F ℂ)) {r : ℝ} (hr : 0 < r)
    {z : ℕ} (hz : 0 < z) (hstable : RelativeStable C z r)
    (hs : ∀ b c : B, ∀ j : Fin 4,
      (j.val : F)*((c : F)-b) ∈ bohr C (relativeWidth C z r))
    (g g' : F → ℝ) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hg' : ∀ x, 0 ≤ g' x ∧ g' x ≤ 1)
    (Q : F → I → F → ℂ) (hQ : ∀ a i x, ‖Q a i x‖ = 1)
    (hpoly : ∀ a i, IsLocallyQuadratic (bohr C r : Set F) (Q a i))
    (H : F → (I → ℂ) → ℝ) (hH : ∀ a v, 0 ≤ H a v ∧ H a v ≤ 1)
    {L : NNReal} (hLip : ∀ a, LipschitzWith L (H a))
    {θ α η ε τ κ : ℝ} (hθ : 0 ≤ θ) (hα : 0 ≤ α)
    (hη : 0 ≤ η) (hε : 0 ≤ ε) (hτ : 0 ≤ τ) (hκ : 0 ≤ κ)
    (hU : uniformityPower 2 (fun x ↦ ((indicator A x-g' x : ℝ) : ℂ)) ≤ η^8)
    (hclose : squaredError g g' ≤ ε^2)
    (hlocal : ∀ a, (𝔼 t : bohr C r, (g (a+t)-H a (fun i ↦ Q a i t))^2) ≤ τ^2)
    (hboundary : τ^2+1/(z : ℝ) ≤ κ^2)
    (hmean : α+modelMeanError N (Fintype.card I) L θ (density (bohr C r)) ≤ density A-η-ε-τ)
    (hnum : modelCountError N (Fintype.card I) z L θ (density (bohr C r)) (density B)+
      4*(η/density B+ε+κ)+density A/(B.card : ℝ) < α^4) :
    ∃ a : F, ∃ χ : AddChar (I → ZMod N) ℂ, χ ≠ 1 ∧
      θ^4 < uniformityPower 1 (mask (bohr C r) (fun x ↦ χ (roundedFactor (Q a) x))) := by
  by_contra! hnone
  obtain ⟨x,d,hd,hpat⟩ := exists_fourAP_of_strong_character_uniform A B hB hv C hr hz hstable hs
    g g' hg hg' Q hQ hpoly H hH hLip hθ hα hη hε hτ hκ hU hclose hlocal hboundary hnone hmean hnum
  exact hd (hfree x d hpat)

#print axioms strong_local_mean_lower
#print axioms fourAP_free_has_bad_local_character
end Erdos3StrongLocalCharacterCriterion
