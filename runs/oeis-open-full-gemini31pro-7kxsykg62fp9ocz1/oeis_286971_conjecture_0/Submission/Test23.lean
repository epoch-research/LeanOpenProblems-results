import Submission.Spec
open Nat

def check_all : IO Unit := do
  for n in [1000:5000] do
    if a n == 0 then
      IO.println s!"Counterexample: {n}"

#eval check_all
