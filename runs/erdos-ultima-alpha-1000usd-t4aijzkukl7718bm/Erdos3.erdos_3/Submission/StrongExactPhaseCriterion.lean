import Submission.AveragedExactPhaseCounting
import Submission.StrongLocalCharacterCriterion

/-! A strong-decomposition counting alternative in exact locally quadratic
phases with bounded integer coefficients. Rank reduction or a density increment
from this alternative is not asserted. -/
namespace Erdos3StrongExactPhaseCriterion
open Finset Erdos3AveragedExactPhaseCounting Erdos3StrongLocalCharacterCriterion
  Erdos3BoundedFrequencyLocalMean Erdos3BoundedFrequencyPhaseApproximation
  Erdos3StrongLocalizedCounting Erdos3StableMaskedUniformity Erdos3FiniteUniformity
  Erdos3CorrelationSifting Erdos3RelativeStableBohr Erdos3FiniteBohr
  Erdos3StableWindowCounting Erdos3LocalQuadraticInverse Erdos3ClippedWeakRegularity
  Erdos3LocalizedPatternCriterion Erdos3UniformityCounting
open scoped BigOperators Classical
set_option maxHeartbeats 7000000
variable {F I : Type*} [Field F] [Fintype F] [Fintype I] [DecidableEq I]
  {N K : ℕ} [NeZero N]

theorem exists_fourAP_of_strong_exact_phase_uniform
    (hKN : K+1 ≤ N) (A B : Finset F) (hB : B.Nonempty)
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
    {σ : ℝ} (hσ : 0 ≤ σ) (hscale : 2/(K+1 : ℝ) ≤ σ^2)
    (hround : 32*density (bohr C r)*(Fintype.card I : ℝ)*(4*K : ℕ)/(N : ℝ) ≤ θ^4/2)
    (hU : uniformityPower 2 (fun x ↦ ((indicator A x-g' x : ℝ) : ℂ)) ≤ η^8)
    (hclose : squaredError g g' ≤ ε^2)
    (hlocal : ∀ a, (𝔼 t : bohr C r, (g (a+t)-H a (fun i ↦ Q a i t))^2) ≤ τ^2)
    (hboundary : τ^2+1/(z : ℝ) ≤ κ^2)
    (hchar : ∀ a, ∀ k : I → ℤ, (∀ i, |k i| ≤ (4*K : ℕ)) → (∃ i, k i ≠ 0) →
      uniformityPower 1 (mask (bohr C r) (fun x ↦ integerPhase k (fun i ↦ Q a i x))) ≤ θ^4/2)
    (hmean : α+cutoffMeanError K N (Fintype.card I) L σ θ (density (bohr C r)) ≤ density A-η-ε-τ)
    (hnum : cutoffCountError K N (Fintype.card I) z L σ θ (density (bohr C r)) (density B)+
      4*(η/density B+ε+κ)+density A/(B.card : ℝ) < α^4) :
    ∃ x d : F, d ≠ 0 ∧ ∀ j : Fin 4, x+(j.val : F)*d ∈ A := by
  have hmean' := strong_local_mean_lower A (bohr C r) ⟨0,bohr_zero C hr.le⟩
    g g' (fun a t ↦ H a (fun i ↦ Q a i t)) hη hε hτ hU hclose hlocal
  have hcount := averaged_exact_phase_count hKN B hB hv C hr hz hstable hs Q hQ hpoly H hH hLip
    hθ hσ hα hscale hround hchar (hmean.trans hmean')
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

/-- Under explicit size/error budgets, a progression-free set forces a
nonzero bounded integer combination of its original local phases to have large
masked U2. This is an exact locally quadratic phase, not a rounded character. -/
theorem fourAP_free_has_bad_exact_phase
    (hKN : K+1 ≤ N) (A B : Finset F) (hB : B.Nonempty)
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
    {σ : ℝ} (hσ : 0 ≤ σ) (hscale : 2/(K+1 : ℝ) ≤ σ^2)
    (hround : 32*density (bohr C r)*(Fintype.card I : ℝ)*(4*K : ℕ)/(N : ℝ) ≤ θ^4/2)
    (hU : uniformityPower 2 (fun x ↦ ((indicator A x-g' x : ℝ) : ℂ)) ≤ η^8)
    (hclose : squaredError g g' ≤ ε^2)
    (hlocal : ∀ a, (𝔼 t : bohr C r, (g (a+t)-H a (fun i ↦ Q a i t))^2) ≤ τ^2)
    (hboundary : τ^2+1/(z : ℝ) ≤ κ^2)
    (hmean : α+cutoffMeanError K N (Fintype.card I) L σ θ (density (bohr C r)) ≤ density A-η-ε-τ)
    (hnum : cutoffCountError K N (Fintype.card I) z L σ θ (density (bohr C r)) (density B)+
      4*(η/density B+ε+κ)+density A/(B.card : ℝ) < α^4) :
    ∃ a : F, ∃ k : I → ℤ, (∀ i, |k i| ≤ (4*K : ℕ)) ∧ (∃ i, k i ≠ 0) ∧
      θ^4/2 < uniformityPower 1 (mask (bohr C r) (fun x ↦ integerPhase k (fun i ↦ Q a i x))) := by
  by_contra! hnone
  obtain ⟨x,d,hd,hpat⟩ := exists_fourAP_of_strong_exact_phase_uniform hKN A B hB hv C hr hz hstable hs
    g g' hg hg' Q hQ hpoly H hH hLip hθ hα hη hε hτ hκ hσ hscale hround hU hclose hlocal hboundary hnone hmean hnum
  exact hd (hfree x d hpat)

#print axioms exists_fourAP_of_strong_exact_phase_uniform
#print axioms fourAP_free_has_bad_exact_phase
end Erdos3StrongExactPhaseCriterion
