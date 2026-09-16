import FormalConjectures.Util.ProblemImports
import Submission.Spec

def check1 (n : ℕ) : Bool :=
  if 0 < n ∧ ¬ (n ∣ 6) then a n > 0 else true

def check2 (n : ℕ) : Bool :=
  (a n = 1) == (n ∈ S)

#eval (List.range 50).all check1
#eval (List.range 50).all check2
