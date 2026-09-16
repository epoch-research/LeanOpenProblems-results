import Submission.Spec
open Nat

partial def check_RHS (n : ℕ) : Bool :=
  let rec check_k (k : ℕ) (pow : ℕ) :=
    if pow > n then false
    else if n % pow == 0 then
      let m := n / pow
      if m = 1 ∨ m = 3 ∨ m = 5 ∨ m = 61 then true
      else check_k (k + 1) (pow * 16)
    else check_k (k + 1) (pow * 16)
  check_k 0 8

def check_conj (n : ℕ) : Bool :=
  let an := a n
  let rhs := check_RHS n
  if an == 0 ∧ rhs == false then false
  else if an > 0 ∧ rhs == true then false
  else if n % 8 != 0 ∧ an == 0 then false
  else true

#eval! (List.range 200).filter (fun n => n > 0 ∧ not (check_conj n))
