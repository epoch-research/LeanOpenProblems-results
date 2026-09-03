import Submission.KloostermanCompletion
/-! Independent checks of weighted Kloosterman completion. -/
open scoped Classical BigOperators
open Erdos821.Kloosterman
#print axioms kloosterman_swap
#print axioms kloosterman_norm_fourth_le_of_ne_zero
#print axioms elementaryBound_nonneg
#print axioms elementaryBound_fourth
#print axioms kloosterman_norm_le
#print axioms fourierMass_nonneg
#print axioms fieldFourier_inversion
#print axioms weightedKloosterman_completion
#print axioms weightedKloosterman_norm_le_of_complete_bound
#print axioms weightedKloosterman_norm_le
example {F : Type*} [Field F] [Fintype F] (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (w : F → ℂ) (a b : F) (hb : b ≠ 0) :
    (Fintype.card F : ℝ)*‖∑ u : Fˣ, w u*ψ (a*(u : F)+b*(u : F)⁻¹)‖ ≤
      Real.sqrt (Real.sqrt (3*(Fintype.card F : ℝ)^3)) *
        ∑ t : F, ‖∑ x : F, w x*ψ (-t*x)‖ :=
  weightedKloosterman_norm_le ψ hψ w a b hb
