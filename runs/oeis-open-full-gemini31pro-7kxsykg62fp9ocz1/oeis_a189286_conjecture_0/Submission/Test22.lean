import Submission.Spec
open Nat

theorem D_divides_T (k m : ℕ) : 
  ((2 * (k + m) : ℤ) - 1) * ((3 * (k + m)).choose (k + m) : ℤ) ∣ (T_term k : ℤ) * (T_term m : ℤ) := by
  sorry
