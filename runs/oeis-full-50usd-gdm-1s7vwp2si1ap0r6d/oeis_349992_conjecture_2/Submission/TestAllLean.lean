import FormalConjectures.Util.ProblemImports
import Submission.Spec

open Nat

-- We want to check if generalized_A349992 a b c m n > 0 for n in [1..1000] for all 11 tuples.
def check_all_tuples_lean : Bool :=
  let tuples : List (ℕ × ℕ × ℕ × ℕ) :=
    [(1,1,11,12), (1,1,11,60), (1,1,14,15), (1,1,23,24), (1,1,23,32),
     (1,1,23,48), (1,2,23,96), (2,1,11,60), (2,1,23,24), (2,1,23,48),
     (4,1,23,48)]
  tuples.all fun t =>
    let a := t.1
    let b := t.2.1
    let c := t.2.2.1
    let m := t.2.2.2
    (List.range 1000).all fun n =>
      if n = 0 then true else
      generalized_A349992 a b c m n > 0

#eval check_all_tuples_lean
