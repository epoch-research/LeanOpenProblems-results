import Mathlib

open Nat

lemma count_test : count Nat.Prime 5 = 2 := by
  have h0 : count Nat.Prime 0 = 0 := count_zero (p := Nat.Prime)
  have p0 : ¬ Nat.Prime 0 := not_prime_zero
  have c1 : count Nat.Prime 1 = 0 := by rw [count_succ, h0, if_neg p0]
  have p1 : ¬ Nat.Prime 1 := not_prime_one
  have c2 : count Nat.Prime 2 = 0 := by rw [count_succ, c1, if_neg p1]
  have p2 : Nat.Prime 2 := prime_two
  have c3 : count Nat.Prime 3 = 1 := by rw [count_succ, c2, if_pos p2]
  have p3 : Nat.Prime 3 := prime_three
  have c4 : count Nat.Prime 4 = 2 := by rw [count_succ, c3, if_pos p3]
  have p4 : ¬ Nat.Prime 4 := by norm_num
  have c5 : count Nat.Prime 5 = 2 := by rw [count_succ, c4, if_neg p4]
  exact c5
