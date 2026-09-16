import Submission.Spec
open Nat Finset

def check_all (n : ℕ) : Bool :=
  (List.range n).all (fun i => if i == 0 then true else A306477 i > 0)

#eval check_all 20
