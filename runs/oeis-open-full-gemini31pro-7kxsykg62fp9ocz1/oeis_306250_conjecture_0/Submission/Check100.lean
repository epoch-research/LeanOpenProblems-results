import Submission.Spec
open Nat Finset

def check100 : Bool :=
  (List.range 100).all fun i => A306250 i > 0

#eval check100
