import Submission.Spec

def main : IO Unit := do
  for i in [0:1000] do
    if A306250 i == 0 then
      IO.println s!"COUNTEREXAMPLE {i}"
      return
  IO.println "No counterexample up to 1000"
