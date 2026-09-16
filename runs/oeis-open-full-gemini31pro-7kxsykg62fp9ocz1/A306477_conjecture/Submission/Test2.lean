import Submission.Spec
open Nat Finset

def checkAll (n : ℕ) : Bool :=
  (List.range n).all (fun i => if i == 0 then true else A306477 i > 0)

#eval checkAll 200
