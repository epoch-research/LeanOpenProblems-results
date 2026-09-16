import Submission.Spec
open Nat BigOperators Int

lemma P_0 : (fun i => Nat.nth Nat.Prime i) 0 = 2 := nth_prime_zero_eq_two
lemma P_1 : (fun i => Nat.nth Nat.Prime i) 1 = 3 := nth_prime_one_eq_three
lemma P_2 : (fun i => Nat.nth Nat.Prime i) 2 = 5 := nth_prime_two_eq_five
