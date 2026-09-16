import Submission.Spec
open Nat Finset

def check1000 : Bool :=
  (List.range 1000).all fun i => A306250 i > 0

#eval check1000
