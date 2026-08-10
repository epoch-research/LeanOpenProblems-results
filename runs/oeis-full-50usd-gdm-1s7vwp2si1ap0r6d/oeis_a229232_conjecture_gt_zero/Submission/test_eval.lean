import FormalConjectures.Util.ProblemImports

open Nat List Finset

def A229232 (n : ℕ) : ℕ :=
  if h_zero : n = 0 then 0
  else
    let N := n
    -- The list of numbers [1, 2, ..., n]
    let l_n : List ℕ := (List.range N).map Nat.succ

    -- The set of all linear permutations of {1, ..., n}.
    let all_perms : Finset (List ℕ) := l_n.permutations.toFinset

    -- Predicate to check if a list satisfies the cyclic prime product minus one property.
    let is_cyclic_prime_chain (p : List ℕ) : Prop :=
      -- rotate (N-1) performs a left rotation by 1, giving the next cyclic element.
      let l_cyclic := p.rotate (N - 1)
      -- zip pairs (a_i, a_{i+1}) cyclically.
      (p.zip l_cyclic).all (fun pair => Nat.Prime (pair.fst * pair.snd - 1))

    -- Filter the permutations based on the decidable prime chain property.
    let good_perms : Finset (List ℕ) :=
      all_perms.filter fun p => decide (is_cyclic_prime_chain p)

    -- The result is the total count of good linear permutations divided by $2n$.
    good_perms.card / (2 * N)

#eval A229232 5
#eval A229232 6
#eval A229232 7
#eval A229232 8
