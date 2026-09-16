import Submission.Spec
open Nat

def check_A : IO Unit := do
  for n in [0:100] do
    let a := A253187 n
    if a == 0 then
      IO.println s!"Counterexample A253187 for n={n}"
      return
  IO.println "check_A done"

#eval check_A
