import FormalConjectures.Util.ProblemImports
import Submission.Spec

def check_k_n (k n : ℕ) : Bool :=
  (List.range n).any fun y =>
    if y = 0 then false
    else
      let x := n - y
      if x = 0 then false
      else
        Nat.Prime (polygonal_number k x + polygonal_number (k + 1) y)

#eval (List.range 20).map fun n => if n ≤ 1 then true else check_k_n 39 n
