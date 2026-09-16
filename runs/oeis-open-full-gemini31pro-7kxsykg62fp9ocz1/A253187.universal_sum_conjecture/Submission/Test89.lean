import Submission.Spec
open Nat Finset

theorem eval_4 : (range (4 + 1)).sum (fun x =>
    (range (4 + 1)).sum fun y =>
      let sum_pent := pentagonal_first x + pentagonal_second y
      if sum_pent <= 4 then
        count_generalized_decagonal_index (4 - sum_pent)
      else
        0) = 1 := by rfl
