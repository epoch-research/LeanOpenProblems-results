import Mathlib
open Nat

noncomputable def A008347_seq : ℕ → ℕ
  | 0 => 0
  | 1 => Nat.nth Nat.Prime 0
  | k + 2 =>
    let p_k_plus_2 := Nat.nth Nat.Prime (k + 1)
    p_k_plus_2 - A008347_seq (k + 1)

theorem s_3 : A008347_seq 3 = 4 := by
  have h1 : A008347_seq 3 = Nat.nth Nat.Prime 2 - A008347_seq 2 := rfl
  have h2 : A008347_seq 2 = Nat.nth Nat.Prime 1 - A008347_seq 1 := rfl
  have h3 : A008347_seq 1 = Nat.nth Nat.Prime 0 := rfl
  rw [h1, h2, h3]
  rw [nth_prime_zero_eq_two, nth_prime_one_eq_three, nth_prime_two_eq_five]
  rfl
