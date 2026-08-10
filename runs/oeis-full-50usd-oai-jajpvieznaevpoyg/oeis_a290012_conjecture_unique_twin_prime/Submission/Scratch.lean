import Submission.Spec

open Nat Set Finset

#check Nat.sInf_mem
#check Nat.sInf_le
#check Nat.exists_prime_lt_and_le_two_mul
#check Nat.add_two_le_nth_prime
#check Nat.nth_le_nth
#check Nat.prime_nth_prime
#check Nat.infinite_setOf_prime

example : A290012 2 = 5 := by
  native_decide

example : ∀ n : ℕ, n < 10 → 1 ≤ n → (A290012 (n+1) = A290012 n + 2 ↔ n = 2) := by
  native_decide
