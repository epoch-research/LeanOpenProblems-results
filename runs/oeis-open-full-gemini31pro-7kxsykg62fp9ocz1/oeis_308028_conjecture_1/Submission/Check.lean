import Submission.Spec
open Nat

def check_range : ℕ → IO Unit
| 0 => pure ()
| n + 1 => do
  if n > 6 then
    let res := A308028 n
    if res == 0 then
      IO.println s!"COUNTEREXAMPLE IN LEAN: n = {n}"
  check_range n

#eval check_range 100
