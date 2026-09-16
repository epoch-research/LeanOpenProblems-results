import Submission.Spec

def print_a : IO Unit := do
  let mut max_a := 0
  for n in [9:51] do
    let val := a n
    if val == 0 then
      IO.println s!"Counterexample: {n}"
    if val > max_a then
      max_a := val
  IO.println s!"Done, max_a = {max_a}"

#eval print_a
