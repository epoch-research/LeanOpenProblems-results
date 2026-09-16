import Submission.Spec
import Mathlib

def check_pos : IO Unit := do
  for n in [0:20] do
    let a := A274007 n
    if a == 0 then
      IO.println s!"Zero at {n}"

#eval check_pos
