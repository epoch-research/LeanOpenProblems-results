import Submission.Spec
open Nat Finset

set_option google.answer "with_auxiliary"
theorem test : ¬ (type_of% @oeis_a271099_conjecture_i) := answer(
  fun h =>
  let h1 := h.2 10
  have h2 : A271099 10 = 1 := by sorry
  have h3 : 10 ∈ A271099_lone_count_set := by decide
  -- wait, A271099 10 = 1 and 10 ∈ lone_count_set. This is ALSO true.
  sorry
)
