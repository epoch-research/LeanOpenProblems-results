import Submission.Spec
open Nat Finset

lemma sum_mod_8 (p_n : ℕ) :
  let R := (Finset.range (p_n + 1)).filter Nat.Prime
  let R1 := R.filter (fun p => p % 8 = 1)
  let R3 := R.filter (fun p => p % 8 = 3)
  let R5 := R.filter (fun p => p % 8 = 5)
  let R7 := R.filter (fun p => p % 8 = 7)
  let R2 := R.filter (fun p => p = 2)
  R.card = R1.card + R3.card + R5.card + R7.card + R2.card := by
  sorry
