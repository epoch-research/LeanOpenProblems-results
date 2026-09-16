import Submission.Spec
open Nat Finset

def check80 : Bool :=
  (List.range 80).all fun i => A306250 i > 0

#eval check80
