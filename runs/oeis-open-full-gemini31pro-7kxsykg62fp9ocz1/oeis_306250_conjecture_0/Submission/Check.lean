import Submission.Spec
open Nat Finset

def check_up_to (n : ℕ) : Bool :=
  (List.range n).all fun i => A306250 i > 0

#eval check_up_to 50
