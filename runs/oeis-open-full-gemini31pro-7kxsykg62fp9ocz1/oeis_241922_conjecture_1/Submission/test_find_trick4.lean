import Submission.Spec
open Nat

#eval (List.range 100).filter (fun n => n % 2 == 0 && n > 2)
