import Submission.Spec
open Nat List Finset
#check fun (p : List (Nat × Nat)) => p.all (fun pair => Nat.Prime (pair.fst * pair.snd - 1))
