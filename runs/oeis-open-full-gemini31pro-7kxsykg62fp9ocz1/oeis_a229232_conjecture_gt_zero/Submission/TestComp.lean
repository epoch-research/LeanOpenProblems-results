import Submission.Spec
open Nat List Finset

def A229232_comp_test (n : ℕ) : ℕ :=
  if h_zero : n = 0 then 0
  else
    let N := n
    let l_n : List ℕ := (List.range N).map Nat.succ
    let all_perms : Finset (List ℕ) := l_n.permutations.toFinset
    let is_cyclic_prime_chain (p : List ℕ) : Prop :=
      let l_cyclic := p.rotate (N - 1)
      (p.zip l_cyclic).all (fun pair => Nat.Prime (pair.fst * pair.snd - 1))
    let good_perms : Finset (List ℕ) :=
      all_perms.filter fun p => decide (is_cyclic_prime_chain p)
    good_perms.card / (2 * N)
