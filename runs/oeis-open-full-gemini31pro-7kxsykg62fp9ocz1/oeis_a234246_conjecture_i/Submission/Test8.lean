import FormalConjectures.Util.ProblemImports
import Submission.Spec

open Finset Nat

def check (n : ℕ) : Bool :=
  let c1 := if 0 < n ∧ ¬ (n ∣ 6) then a n > 0 else true
  let c2 := (a n = 1) == (n ∈ S)
  c1 && c2

#eval! (List.range 5000).all check
