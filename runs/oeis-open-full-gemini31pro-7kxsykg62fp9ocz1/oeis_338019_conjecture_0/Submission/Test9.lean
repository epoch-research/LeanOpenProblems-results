import Submission.Spec
open Nat Finset

partial def check_RHS (n : ℕ) : Bool :=
  let rec check_k (k : ℕ) (pow : ℕ) :=
    if pow > n then false
    else if n % pow == 0 then
      let m := n / pow
      if m = 1 ∨ m = 3 ∨ m = 5 ∨ m = 61 then
        if (m % 2 != 0) then true
        else check_k (k + 1) (pow * 16)
      else check_k (k + 1) (pow * 16)
    else check_k (k + 1) (pow * 16)
  check_k 0 8

partial def conj_holds (n : ℕ) : Bool :=
  if n == 0 then true else
  let an := a n
  let rhs := check_RHS n
  let part1 := (an == 0) == rhs
  let part2 := (n % 8 == 0) || (an > 0)
  part1 && part2

#eval! (List.range 100).all conj_holds
