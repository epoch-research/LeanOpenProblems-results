import Submission.Spec
open Nat BigOperators Int

theorem A092243_2_eq : A092243 2 = 1 := by
  dsimp [A092243]
  have p0 : nth Nat.Prime 0 = 2 := nth_prime_zero_eq_two
  have p1 : nth Nat.Prime 1 = 3 := nth_prime_one_eq_three
  have p2 : nth Nat.Prime 2 = 5 := nth_prime_two_eq_five
  sorry
