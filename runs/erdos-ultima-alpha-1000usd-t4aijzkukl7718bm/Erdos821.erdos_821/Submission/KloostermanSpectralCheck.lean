import Submission.KloostermanSpectral
/-! Independent checks of signed Kloosterman spectral estimates. -/
open scoped Classical BigOperators
open Erdos821.Kloosterman
#print axioms sum_units_add_zero
#print axioms positiveTransform_correlation
#print axioms positiveTransform_energy
#print axioms positiveTransform_units_energy
#print axioms centeredEnergy_nonneg
#print axioms positiveTransform_inverse_units_energy
#print axioms bilinearKloosterman_factorization
#print axioms norm_sum_mul_sq_le
#print axioms bilinearKloosterman_centered_bound
#print axioms positiveTransform_wave
#print axioms centeredEnergy_wave
#print axioms bilinearKloosterman_waves
example {F : Type*} [Field F] [Fintype F] (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (α β : F → ℂ) :
    ‖∑ a : F, ∑ b : F, α a*β b*(∑ u : Fˣ, ψ (a*(u : F)+b*(u : F)⁻¹))‖^2 ≤
      ((Fintype.card F : ℝ)*(∑ a : F, ‖α a‖^2)-‖∑ a : F, α a‖^2) *
      ((Fintype.card F : ℝ)*(∑ b : F, ‖β b‖^2)-‖∑ b : F, β b‖^2) :=
  bilinearKloosterman_centered_bound ψ hψ α β
