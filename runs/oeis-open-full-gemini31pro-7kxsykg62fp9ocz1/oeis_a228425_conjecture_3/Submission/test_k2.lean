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

#eval check_k2 2
#eval check_k2 3
#eval check_k2 4
#eval check_k2 8
#eval check_k2 14
