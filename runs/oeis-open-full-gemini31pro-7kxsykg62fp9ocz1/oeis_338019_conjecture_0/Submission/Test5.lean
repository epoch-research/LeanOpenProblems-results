import Submission.Spec
open Nat

def check_RHS (n : ℕ) : Bool :=
  let rec check_k (k : ℕ) (pow : ℕ) :=
    if pow > n then false
    else if n % pow == 0 then
      let m := n / pow
      if m = 1 ∨ m = 3 ∨ m = 5 ∨ m = 61 then
        if m % 2 != 0 ∧ (n / pow) % 2 != 0 then true -- Wait, n/pow is m, which is odd! So 2-adic val is exactly k.
        -- Actually, n = 2^(4k+3) * m. So pow = 2^(4k+3).
        -- We need to check if n % (pow * 2) != 0 to ensure exact power?
        -- Yes, because if n % (pow * 2) == 0, then m is even, so m can't be 1,3,5,61 anyway!
        else check_k (k + 1) (pow * 16)
      else check_k (k + 1) (pow * 16)
    else check_k (k + 1) (pow * 16)
  check_k 0 8

def check_conj (n : ℕ) : Bool :=
  if n == 0 then true else
  let an := a n
  let rhs := check_RHS n
  if an == 0 ∧ rhs == false then false
  else if an > 0 ∧ rhs == true then false
  else if n % 8 != 0 ∧ an == 0 then false
  else true

#eval! (List.range 200).filter (fun n => not (check_conj n))
