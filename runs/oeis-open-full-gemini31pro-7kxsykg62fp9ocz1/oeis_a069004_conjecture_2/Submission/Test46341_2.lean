import Mathlib
import Submission.Spec

def print_a : IO Unit := do
  IO.println s!"a 46341 = {a 46341}"
  IO.println s!"pi 46341 = {Nat.primeCounting 46341}"

#eval print_a
