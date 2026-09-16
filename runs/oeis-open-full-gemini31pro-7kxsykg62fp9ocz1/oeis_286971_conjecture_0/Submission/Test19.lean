import Submission.Spec
open Nat

def check_all : IO Unit := do
  for n in [30:50] do
    IO.println s!"a({n}) = {a n}"

#eval check_all
