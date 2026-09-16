import Submission.Spec
open Nat Finset

def is_sq (n : ℕ) : Bool :=
  n.sqrt * n.sqrt == n

def a_prog (n : ℕ) : ℕ :=
  let M := n.sqrt
  let R := range (M + 1)
  let BoundingBox := (R.product R).product (R.product R)
  (BoundingBox.filter (fun p =>
    let ((x, y), (z, w)) := p
    x^2 + y^2 + z^2 + w^2 == n ∧
    let c := 3 * x + 10 * y + 36 * z
    c > 0 ∧ is_sq c
  )).card

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

def is_counterexample (n : ℕ) : Bool :=
  if n == 0 then false else
  let an := a_prog n
  let rhs := check_RHS n
  if an == 0 ∧ rhs == false then true
  else if an > 0 ∧ rhs == true then true
  else if n % 8 != 0 ∧ an == 0 then true
  else false

#eval! (List.range 200).filter is_counterexample
#eval! (List.range 200).map (· + 200) |>.filter is_counterexample
#eval! (List.range 200).map (· + 400) |>.filter is_counterexample
