import Submission.Spec

def check (n : Nat) : Bool :=
  a n == 0

#eval (List.range 100).filter check
