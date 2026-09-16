import Submission.Spec
open Nat Finset

def check_conj (n : ℕ) : Bool :=
  let an := a n
  let bn := b n
  an == 0 && bn < 0

-- #eval (List.range 100).filter check_conj
