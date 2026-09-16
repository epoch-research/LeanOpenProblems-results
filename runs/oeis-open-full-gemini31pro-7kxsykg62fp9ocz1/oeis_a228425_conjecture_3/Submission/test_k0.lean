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

def find_fail (k max_n : ℕ) : ℕ :=
  let res := (List.range max_n).find? fun n =>
    if n ≤ 1 then false else not (check_k_n k n)
  match res with
  | some n => n
  | none => 0

#eval find_fail 0 100
#eval find_fail 1 100
