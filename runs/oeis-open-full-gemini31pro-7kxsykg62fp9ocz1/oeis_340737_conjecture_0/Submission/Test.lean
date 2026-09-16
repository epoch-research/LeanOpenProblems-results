import Submission.Spec
import Lean

def evalA : IO Unit := do
  for i in [1:15] do
    let a := A340737 i
    let b := A340738 i
    IO.println s!"{i}: {a} / {b}"

#eval evalA
