import Submission.Spec

open Nat Finset

#eval (List.range 150).all (fun n =>
  let an := A261627 n
  let cond1 := if n > 6 then an > 0 else true
  let cond2 := (an == 1) == (n ∈ A261627_singletons)
  cond1 && cond2
)
