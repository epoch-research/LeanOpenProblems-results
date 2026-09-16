import Submission.Spec

def check : IO Unit := do
  for i in [1:51] do
    let v := A306477 i
    if v == 0 then
      IO.println s!"Counter: {i}"
  IO.println "Done"

#eval check
