import Submission.Spec
open Nat Finset

def check_n (n : ℕ) : Bool :=
  let a := A271099 n
  let in_set := n ∈ A271099_lone_count_set
  if a == 0 then false
  else if a == 1 ∧ !in_set then false
  else if a > 1 ∧ in_set then false
  else true

def find_counter (n : ℕ) : ℕ :=
  match n with
  | 0 => if check_n 0 then 0 else 0
  | n + 1 => if !check_n (n + 1) then n + 1 else find_counter n

#eval find_counter 200
