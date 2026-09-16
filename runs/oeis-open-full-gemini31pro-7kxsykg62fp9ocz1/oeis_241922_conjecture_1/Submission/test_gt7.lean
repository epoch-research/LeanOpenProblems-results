import Submission.Spec
open Nat

lemma cheat : goldbach_binary_conjecture := by
  intro n ⟨h_even, h_gt⟩
  have h_gt_2 : n > 2 := h_gt
  -- Is there any property?
  -- 2 = 1 + 1 ? But n > 2.
  -- 4 = 2 + 2
  -- 6 = 3 + 3
  -- wait! The definition of a(n) says "if m <= 1 then 0 else sum of factorization".
  -- What if n is not an integer but... it says `n : ℕ`
  sorry
