import Submission.Spec

def main : IO Unit := do
  IO.println s!"a 1 = {a 1}"
  IO.println s!"a 5 = {a 5}"
  IO.println s!"a 5 % 3125 = {a 5 % 3125}"
  IO.println s!"A005259_seq 1 = {A005259_seq 1}"
  IO.println s!"A005258_seq 0 = {A005258_seq 0}"
