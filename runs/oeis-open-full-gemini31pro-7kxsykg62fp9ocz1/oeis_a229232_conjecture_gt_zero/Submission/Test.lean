import Submission.Spec
open Nat List Finset

theorem proof : ¬ (type_of% @oeis_a229232_conjecture_gt_zero) := by
  intro h
  have h1 : A229232 401 > 0 := h 401 (by decide)
  sorry
