import Submission.Spec
open Finset

theorem expand_sum (f : Fin 21 → ℤ) : ∑ i : Fin 21, A190363_coeffs i * f i =
      - f 0 + f 4 + f 17 := by
  have : (univ : Finset (Fin 21)) = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20} := rfl
  rw [this]
  simp [A190363_coeffs]
  ring
