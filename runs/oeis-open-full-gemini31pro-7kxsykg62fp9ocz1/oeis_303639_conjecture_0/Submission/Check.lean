import Mathlib

def is_sq (n : Nat) : Bool :=
  let s := n.sqrt
  s * s == n

def check_sum_sq (R : Nat) : Bool :=
  Id.run <| do
    let mut res := false
    let s := R.sqrt
    for a in [0:s+1] do
      if is_sq (R - a * a) then
        res := true
    return res

#eval check_sum_sq (800322180 - 1 - 1)
