import Submission.Spec
open Nat List Finset

#check fun (p : List ℕ) (N : ℕ) =>
  let l_cyclic := p.rotate (N - 1)
  (p.zip l_cyclic).all (fun pair => Nat.Prime (pair.fst * pair.snd - 1))
