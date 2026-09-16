import Submission.Spec
open Nat Finset

def check200 : Bool :=
  (List.range 200).all fun i => A306250 i > 0

#eval check200
