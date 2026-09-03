import Submission.StrongExactPhaseCriterion

/-! The exact local phase obstruction has a normalized linear Fourier
certificate. Its local quadraticity is retained; no rank-reduction theorem
or summable density increment is inferred from correlation alone. -/
namespace Erdos3ExactPhaseLinearObstruction
open Finset Erdos3StrongExactPhaseCriterion Erdos3BoundedFrequencyPhaseApproximation
  Erdos3StableMaskedUniformity Erdos3FiniteUniformity Erdos3FiniteFourier
  Erdos3CorrelationSifting Erdos3LocalQuadraticInverse
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 6000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- U2 is at most the largest squared Fourier coefficient times the exact
L2 energy, without discarding the support density. -/
lemma exists_large_fourier_with_energy (f : G → ℂ) :
    ∃ ψ : AddChar G ℂ,
      uniformityPower 1 f ≤ ‖hat f ψ‖^2*(𝔼 x : G, ‖f x‖^2) := by
  obtain ⟨ψ,_,hψ⟩ := exists_max_image univ (fun χ : AddChar G ℂ ↦ ‖hat f χ‖^2) univ_nonempty
  refine ⟨ψ,?_⟩
  rw [uniformityPower_one_fourier]
  calc
    _ ≤ ∑ χ : AddChar G ℂ, ‖hat f ψ‖^2*‖hat f χ‖^2 := by
      apply sum_le_sum
      intro χ hχ
      have h := mul_le_mul_of_nonneg_right (hψ χ hχ) (sq_nonneg ‖hat f χ‖)
      nlinarith only [h]
    _ = _ := by rw [← mul_sum,parseval]

lemma mask_unit_energy (W : Finset G) (q : G → ℂ) (hq : ∀ x, ‖q x‖ = 1) :
    (𝔼 x : G, ‖mask W q x‖^2) = density W := by
  rw [← expect_indicator]
  apply expect_congr rfl
  intro x _
  by_cases hx : x ∈ W <;> simp only [mask,indicator,hx,if_true,if_false,hq,one_pow,norm_zero,zero_pow (by decide : 2 ≠ 0)]

lemma mask_hat_normalized (W : Finset G) (hW : W.Nonempty) (q : G → ℂ)
    (ψ : AddChar G ℂ) :
    hat (mask W q) ψ = (density W : ℂ)*(𝔼 t : W, q t*conj (ψ t)) := by
  unfold hat
  rw [supported_expect W hW _ (fun x hx ↦ by simp only [mask,if_neg hx,zero_mul])]
  congr 1
  apply expect_congr rfl
  intro t _
  simp only [mask,if_pos t.property]

/-- A unit local phase with large masked U2 correlates with a linear character
on the normalized window. The precise density factor is density(W)^3. -/
theorem local_phase_fourier_certificate (W : Finset G) (hW : W.Nonempty)
    (q : G → ℂ) (hq : ∀ x, ‖q x‖ = 1) :
    ∃ ψ : AddChar G ℂ,
      uniformityPower 1 (mask W q) ≤
        (density W)^3*‖𝔼 t : W, q t*conj (ψ t)‖^2 := by
  obtain ⟨ψ,hψ⟩ := exists_large_fourier_with_energy (mask W q)
  refine ⟨ψ,?_⟩
  rw [mask_unit_energy W q hq,mask_hat_normalized W hW q ψ,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (density_nonneg W),mul_pow] at hψ
  convert hψ using 1 <;> ring

variable {I X : Type*} [Fintype I] [DecidableEq I]

/-- Converts the new counting obstruction into an exact locally quadratic
phase with bounded integer coefficients and a nonzero linear correlation. -/
theorem exact_phase_linear_certificate (W : Finset G) (hW : W.Nonempty)
    (Q : X → I → G → ℂ) (hQ : ∀ a i x, ‖Q a i x‖ = 1)
    (hpoly : ∀ a i, IsLocallyQuadratic (W : Set G) (Q a i))
    {R : ℕ} {δ : ℝ}
    (hbad : ∃ a : X, ∃ k : I → ℤ, (∀ i, |k i| ≤ R) ∧ (∃ i, k i ≠ 0) ∧
      δ < uniformityPower 1 (mask W (fun x ↦ integerPhase k (fun i ↦ Q a i x)))) :
    ∃ a : X, ∃ k : I → ℤ, ∃ ψ : AddChar G ℂ,
      (∀ i, |k i| ≤ R) ∧ (∃ i, k i ≠ 0) ∧
      IsLocallyQuadratic (W : Set G) (fun x ↦ integerPhase k (fun i ↦ Q a i x)) ∧
      δ < (density W)^3*‖𝔼 t : W, integerPhase k (fun i ↦ Q a i t)*conj (ψ t)‖^2 := by
  obtain ⟨a,k,hk,hkn,hU⟩ := hbad
  obtain ⟨ψ,hψ⟩ := local_phase_fourier_certificate W hW
    (fun x ↦ integerPhase k (fun i ↦ Q a i x)) (fun x ↦ integerPhase_norm k _ (fun i ↦ hQ a i x))
  exact ⟨a,k,ψ,hk,hkn,integerPhase_locally_quadratic k (Q a) (hpoly a),hU.trans_le hψ⟩

#print axioms local_phase_fourier_certificate
#print axioms exact_phase_linear_certificate
end Erdos3ExactPhaseLinearObstruction
