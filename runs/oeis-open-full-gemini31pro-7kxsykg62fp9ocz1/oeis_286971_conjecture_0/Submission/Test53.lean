import Submission.Spec
open ArithmeticFunction

def check_all : IO Unit := do
  for n in [11:100] do
    if a n == 0 then
      IO.println s!"Counterexample: {n}"

#eval check_all
