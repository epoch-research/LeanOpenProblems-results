import FormalConjectures.Util.ProblemImports
import Submission.Spec

open Nat

def check_k2 (n : ℕ) : Bool :=
  if n ≤ 1 then true
  else
    let res := (List.range n).any fun y =>
      if y = 0 then false
      else
        let x := n - y
        if x = 0 then false
        else
          (x + y * (y + 1) / 2).Prime
    res

def check_all_k2 (max_n : ℕ) : Bool :=
  (List.range max_n).all fun n => check_k2 n

#eval check_all_k2 1000
