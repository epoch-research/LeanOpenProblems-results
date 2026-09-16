import Submission.Spec
open Nat List Finset
#check (fun pair : Nat × Nat => Nat.Prime (pair.fst * pair.snd - 1))
