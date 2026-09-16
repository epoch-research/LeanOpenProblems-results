import FormalConjectures.Util.ProblemImports
import Submission.Spec

def check_k (k n : ℕ) : Bool :=
  (List.range n).any fun y =>
    if y = 0 then false
    else
      let x := n - y
      if x = 0 then false
      else
        Nat.Prime (polygonal_number k x + polygonal_number (k + 1) y)

def check_all (k max_n : ℕ) : Bool :=
  (List.range max_n).all fun n =>
    if n ≤ 1 then true else check_k k n

#eval check_all 39 1000
#eval check_all 99 1000
