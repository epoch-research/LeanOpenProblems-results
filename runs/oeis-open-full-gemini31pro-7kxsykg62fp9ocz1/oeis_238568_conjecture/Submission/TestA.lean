import FormalConjectures.Util.ProblemImports
import Submission.TestCardProp3
import Submission.Spec

open Finset Nat

lemma a_eq_card (n : ℕ) : a n = (Finset.filter (fun k : ℕ => Nat.Prime (Nat.pow n 2 - (Finset.filter Nat.Prime (Finset.Iic (k * n))).card)) (Finset.Ico 1 n)).card := by
  unfold a
  congr 2
  ext k
  simp only [pi_fn_eq_card]
