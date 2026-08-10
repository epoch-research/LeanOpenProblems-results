import FormalConjectures.Util.ProblemImports
open Nat Finset
#check (fun a b n : ℕ => 2 ^ a * 3 ^ b ≤ n ∧ Nat.Prime (6 * (n - 2 ^ a * 3 ^ b) + 1))
#check (fun a b n : ℕ => 2 ^ a * 3 ^ b < n ∧ Nat.Prime (6 * (n - 2 ^ a * 3 ^ b) - 1))
#print axioms Nat.forall_exists_prime_gt_and_modEq
#print axioms Nat.exists_prime_lt_and_le_two_mul
