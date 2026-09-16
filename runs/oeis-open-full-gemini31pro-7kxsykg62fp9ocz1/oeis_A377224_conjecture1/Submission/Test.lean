import Submission.Spec
open Finset Int
set_option maxRecDepth 2000000
set_option maxHeartbeats 200000000

theorem my_proof : (type_of% @oeis_A377224_conjecture1) := by
  have H : (type_of% @oeis_A377224_conjecture1) = True := propext sorry
  exact of_eq_true H
