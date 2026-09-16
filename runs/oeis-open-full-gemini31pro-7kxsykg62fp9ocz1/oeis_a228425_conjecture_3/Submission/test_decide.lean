import Mathlib

def polygonal_number (m x : ℕ) : ℕ :=
  (m - 2) * x * (x - 1) / 2 + x

def check_k (k n : ℕ) : Bool :=
  (List.range n).any fun y =>
    if y = 0 then false
    else
      let x := n - y
      if x = 0 then false
      else
        Nat.Prime (polygonal_number k x + polygonal_number (k + 1) y)

#eval check_k 99 2
#eval check_k 99 3
#eval check_k 99 4
#eval check_k 99 5
