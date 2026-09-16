import Submission.Spec
open Nat Finset

theorem check_the_proof_with_sorry6 : (type_of% @A253187.universal_sum_conjecture) := by
  constructor
  · intro n
    sorry
  · intro k m h n
    cases h
    -- Wait, what happens if we just sorry the rest?
    sorry
