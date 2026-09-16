import Submission.Spec

def print_20 : IO Unit := do
  for n in [0:20] do
    let a := A274007 n
    IO.println s!"n={n}: {a}"

#eval print_20
