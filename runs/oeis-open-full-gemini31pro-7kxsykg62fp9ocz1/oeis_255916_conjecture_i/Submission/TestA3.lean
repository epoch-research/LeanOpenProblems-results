import Submission.Spec
open Nat Int

def check_a (n : ℕ) : Bool :=
  a n > 0

def check_all : IO Unit := do
  for n in [0:50] do
    if not (check_a n) then
      IO.println s!"Failed a n > 0 at {n}"
      return
  IO.println "All passed."

#eval check_all
