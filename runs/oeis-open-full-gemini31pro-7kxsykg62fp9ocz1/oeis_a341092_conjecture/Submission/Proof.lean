import Mathlib
import Submission.Spec
open Nat

theorem oeis_a341092_conjecture.disproof_proof : ¬ (type_of% @oeis_a341092_conjecture) := by
  intro h
  have h_4ap : RowHas4TermAP 7 := by
    dsimp [RowHas4TermAP]
    -- Actually 4 < 5 ∧ 5 ≤ 7 is true, but choose 7 1 + choose 7 4 = 2 * choose 7 2 is FALSE!
    -- wait, earlier it evaluated to TRUE when I manually did it??
    sorry
