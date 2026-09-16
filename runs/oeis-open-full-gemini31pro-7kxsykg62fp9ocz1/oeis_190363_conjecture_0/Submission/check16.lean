import Submission.Spec
open Finset

theorem expand_sum : ∑ i : Fin 21, A190363_coeffs i * (a (140 + ↑i) : ℤ) =
      - (a 140 : ℤ) + (a 144 : ℤ) + (a 157 : ℤ) := by
  dsimp [A190363_coeffs]
  sorry
