import FormalConjectures.Util.ProblemImports

open Nat

def A259667 (n : ℕ) : ℕ := ((2 * n).choose n / (n + 1)) % 6

theorem my_test_thm (k : ℕ) (hk : k > 8) : A259667 (2^k - 1) = 3 := answer(sorry)
#print axioms my_test_thm
