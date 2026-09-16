import Submission.Spec
open Nat

def check_all : IO Unit := do
  let ones := [3, 5, 9, 10, 17, 20, 24, 25, 31, 36, 45, 73, 80, 101, 136, 145, 388, 649]
  for n in [7 : 100] do
    let a := A262781 n
    if a == 0 then
      IO.println s!"Counter (i): {n}"
    if a == 1 ∧ !ones.contains n then
      IO.println s!"Counter (ii): {n}"
    if a != 1 ∧ ones.contains n then
      IO.println s!"Counter (ii) in ones: {n}, a={a}"
  IO.println "Done"

#eval check_all
