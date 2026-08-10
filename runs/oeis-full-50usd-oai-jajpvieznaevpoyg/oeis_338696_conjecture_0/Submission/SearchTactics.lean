import FormalConjectures.Util.ProblemImports
open Nat BigOperators Finset

example (n : ℕ) : ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n := by
  exact Nat.sum_four_squares n

-- Try exact? / library_search? for binary form not expected.
example (n : ℕ) : (∃ x y : ℕ, n = x ^ 2 + y ^ 2) ↔ ∀ q ∈ n.primeFactors, q % 4 = 3 → Even (padicValNat q n) := by
  exact Nat.eq_sq_add_sq_iff

#check? Nat.eq_sq_add_sq_iff
#check? ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one
#check? legendreSym.quadratic_reciprocity
