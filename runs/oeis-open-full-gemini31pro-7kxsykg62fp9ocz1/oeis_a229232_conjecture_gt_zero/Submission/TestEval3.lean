import Submission.Spec
open Nat List Finset

def A229232_comp (n : ℕ) : ℕ :=
  if h_zero : n = 0 then 0
  else
    let N := n
    let l_n : List ℕ := (List.range N).map Nat.succ
    let all_perms : List (List ℕ) := l_n.permutations
    let is_cyclic_prime_chain (p : List ℕ) : Bool :=
      let l_cyclic := p.rotate (N - 1)
      (p.zip l_cyclic).all (fun pair => decide (Nat.Prime (pair.fst * pair.snd - 1)))
    let good_perms := all_perms.filter is_cyclic_prime_chain
    good_perms.length / (2 * N)

#eval A229232_comp 5
#eval A229232_comp 6
#eval A229232_comp 7
#eval A229232_comp 8
