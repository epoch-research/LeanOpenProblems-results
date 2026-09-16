import Submission.Spec
open Nat

def checkAll : IO Unit := do
  for n in [0:1000] do
    if A253187 n == 0 then
      IO.println s!"Failed at {n}"
  IO.println "Done"

#eval checkAll
