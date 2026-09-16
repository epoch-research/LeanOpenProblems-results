import Submission.Spec
open Nat

def checkMissing : IO Unit := do
  let mut seen : Array Bool := mkArray 1000 false
  for n in [1:100000] do
    let val := a n
    if val < 1000 then
      seen := seen.set! val true
  
  let mut missing := 0
  for k in [1:1000] do
    if not (seen.get! k) then
      IO.println s!"Missing: {k}"
      missing := missing + 1
  if missing == 0 then
    IO.println "All up to 999 found."

def main : IO Unit := checkMissing
