import Submission.KloostermanFourthMoment
/-! Independent checks of the finite-field Kloosterman estimates. -/
open scoped Classical
open Erdos821.Kloosterman
#print axioms pair_eq_or_swap_of_sum_invSum
#print axioms collides_eq_or_swap
#print axioms collisionFiber_card_le_two
#print axioms collisionFiber_card_le_units
#print axioms zero_pairSum_card_le_units
#print axioms collisionEnergy_le
#print axioms kloosterman_sq
#print axioms conj_char
#print axioms kloosterman_norm_fourth_expansion
#print axioms sum_char_two_frequencies
#print axioms kloosterman_fourth_moment
#print axioms kloosterman_rescale
#print axioms rescale_injective
#print axioms rescale_moment_le
#print axioms kloosterman_norm_fourth_le_units
#print axioms kloosterman_norm_fourth_le
example {F : Type*} [Field F] [Fintype F] (ψ : AddChar F ℂ)
    (hψ : ψ.IsPrimitive) (a b : F) (ha : a ≠ 0) :
    ‖∑ u : Fˣ, ψ (a*(u : F) + b*(u : F)⁻¹)‖^4 ≤
      3*(Fintype.card F : ℝ)^3 :=
  kloosterman_norm_fourth_le ψ hψ a b ha
