import Submission.Spec

def find_counterexample : IO Unit := do
  for n in [1:100000] do
    let c := A270966 n
    if c == 0 then
      IO.println s!"Counterexample 0: {n}"
      return
    if c == 1 ∧ n ≠ 1 ∧ n ≠ 49 ∧ n ≠ 608 then
      IO.println s!"Counterexample 1: {n}"
      return
    if n % 1000 == 0 then
      IO.println s!"Checked {n}"

#eval find_counterexample
