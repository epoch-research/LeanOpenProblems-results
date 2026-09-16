import Submission.Spec
open ArithmeticFunction

def print_mu : IO Unit := do
  for i in [1:20] do
    IO.println s!"mu({i}) = {moebius i}"

#eval print_mu
