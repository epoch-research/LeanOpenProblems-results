import Submission.Spec
open Nat Finset

lemma sum_mod_8 (p_n : ℕ) :
  let R := (Finset.range (p_n + 1)).filter Nat.Prime
  let count (b : ℕ) := (R.filter (fun p => p % 8 = b)).card
  R.card = count 1 + count 3 + count 5 + count 7 + count 2 := by
  sorry
