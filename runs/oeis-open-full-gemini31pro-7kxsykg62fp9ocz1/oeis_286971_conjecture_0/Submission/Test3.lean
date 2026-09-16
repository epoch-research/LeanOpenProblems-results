import Submission.Spec
open Nat

def find_counterexample : IO Unit := do
  for n in [11:10000] do
    if a n == 0 then
      IO.println s!"Counterexample: {n}"

#eval find_counterexample
