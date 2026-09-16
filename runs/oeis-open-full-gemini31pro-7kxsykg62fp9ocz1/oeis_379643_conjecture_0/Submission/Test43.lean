import Submission.Spec
open Nat Finset

def check_n (n : ℕ) : Bool :=
  let p_n := Nat.nth Nat.Prime (n - 1)
  let count (b : ℕ) := ((Finset.range (p_n + 1)).filter (fun p => Nat.Prime p ∧ p % 8 = b)).card
  let a := (count 3 : ℤ) - (count 7 : ℤ)
  let b := (count 5 : ℤ) - (count 1 : ℤ)
  a == 0 && b < 0

#eval (List.range 100).map check_n
