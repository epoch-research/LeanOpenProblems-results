import Submission.Spec
import Mathlib

def main : IO Unit := do
  for n in [287:10000000+1] do
    if a n <= 1 then
      IO.println s!"Counterexample: {n}"
      return
    if n % 100000 == 0 then
      IO.println s!"Progress: {n}"
  IO.println "Finished"
