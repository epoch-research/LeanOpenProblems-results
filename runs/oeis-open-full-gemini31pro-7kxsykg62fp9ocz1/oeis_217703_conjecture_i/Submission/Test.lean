import Submission.Spec
open Int
open Polynomial

theorem test : ∀ (n : ℕ), 1 ≤ n → Irreducible (Polynomial.map (Int.castRingHom ℚ) (Sn n)) := by
  sorry
