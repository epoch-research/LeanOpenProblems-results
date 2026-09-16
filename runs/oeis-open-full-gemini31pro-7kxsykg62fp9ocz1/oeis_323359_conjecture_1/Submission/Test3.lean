import Submission.Spec
open Nat

def check_all : ℕ → Bool
| 0 => true
| n + 1 =>
  let an := a (n + 1)
  if an == 1 || an.Prime then check_all n
  else false

#eval! check_all 2000
