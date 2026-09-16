import Mathlib
import Submission.Spec
open Nat

lemma nth_prime_6_eq_17 : nth Nat.Prime 6 = 17 := by sorry
lemma nth_prime_10_eq_31 : nth Nat.Prime 10 = 31 := by sorry

set_option maxRecDepth 200000

lemma test_A : A237413 6 = 1 := by
  dsimp [A237413]
  have h_ico : Finset.Ico 1 6 = {1, 2, 3, 4, 5} := rfl
  rw [h_ico]
  have h_sum : (∑ k ∈ ({1, 2, 3, 4, 5} : Finset ℕ),
      if
          Nat.Prime (nth Nat.Prime (k - 1) ^ 2 - 2) ∧
            Nat.Prime (nth Nat.Prime (6 - k - 1) ^ 2 - 2) ∧
              Nat.Prime (nth Nat.Prime (nth Nat.Prime (6 - k - 1) - 1) ^ 2 - 2) then
        1
      else 0) =
    (if Nat.Prime (nth Nat.Prime 0 ^ 2 - 2) ∧ Nat.Prime (nth Nat.Prime 4 ^ 2 - 2) ∧ Nat.Prime (nth Nat.Prime (nth Nat.Prime 4 - 1) ^ 2 - 2) then 1 else 0) +
    ((if Nat.Prime (nth Nat.Prime 1 ^ 2 - 2) ∧ Nat.Prime (nth Nat.Prime 3 ^ 2 - 2) ∧ Nat.Prime (nth Nat.Prime (nth Nat.Prime 3 - 1) ^ 2 - 2) then 1 else 0) +
    ((if Nat.Prime (nth Nat.Prime 2 ^ 2 - 2) ∧ Nat.Prime (nth Nat.Prime 2 ^ 2 - 2) ∧ Nat.Prime (nth Nat.Prime (nth Nat.Prime 2 - 1) ^ 2 - 2) then 1 else 0) +
    ((if Nat.Prime (nth Nat.Prime 3 ^ 2 - 2) ∧ Nat.Prime (nth Nat.Prime 1 ^ 2 - 2) ∧ Nat.Prime (nth Nat.Prime (nth Nat.Prime 1 - 1) ^ 2 - 2) then 1 else 0) +
    (if Nat.Prime (nth Nat.Prime 4 ^ 2 - 2) ∧ Nat.Prime (nth Nat.Prime 0 ^ 2 - 2) ∧ Nat.Prime (nth Nat.Prime (nth Nat.Prime 0 - 1) ^ 2 - 2) then 1 else 0)))) := by rfl
  rw [h_sum]
  have hp0 : nth Nat.Prime 0 = 2 := nth_prime_zero_eq_two
  have hp1 : nth Nat.Prime 1 = 3 := nth_prime_one_eq_three
  have hp2 : nth Nat.Prime 2 = 5 := Nat.nth_prime_two_eq_five
  have hp3 : nth Nat.Prime 3 = 7 := nth_prime_three_eq_seven
  have hp4 : nth Nat.Prime 4 = 11 := nth_prime_four_eq_eleven
  have hp10 : nth Nat.Prime 10 = 31 := nth_prime_10_eq_31
  have hp6 : nth Nat.Prime 6 = 17 := nth_prime_6_eq_17
  
  rw [hp0, hp1, hp2, hp3, hp4]
  rw [hp10, hp6]
  
  have hd1 : (if (Nat.Prime (2 ^ 2 - 2) ∧ Nat.Prime (11 ^ 2 - 2) ∧ Nat.Prime (31 ^ 2 - 2)) then 1 else 0) = 0 := by
    have h1 : ¬ Nat.Prime 119 := by decide
    exact if_neg (fun h => h1 h.2.1)
  have hd2 : (if (Nat.Prime (3 ^ 2 - 2) ∧ Nat.Prime (7 ^ 2 - 2) ∧ Nat.Prime (17 ^ 2 - 2)) then 1 else 0) = 0 := by
    have h2 : ¬ Nat.Prime 287 := by decide
    exact if_neg (fun h => h2 h.2.2)
  have hd3 : (if (Nat.Prime (5 ^ 2 - 2) ∧ Nat.Prime (5 ^ 2 - 2) ∧ Nat.Prime (11 ^ 2 - 2)) then 1 else 0) = 0 := by
    have h3 : ¬ Nat.Prime 119 := by decide
    exact if_neg (fun h => h3 h.2.2)
  have hd4 : (if (Nat.Prime (7 ^ 2 - 2) ∧ Nat.Prime (3 ^ 2 - 2) ∧ Nat.Prime (5 ^ 2 - 2)) then 1 else 0) = 1 := by
    have h4_1 : Nat.Prime 47 := by decide
    have h4_2 : Nat.Prime 7 := by decide
    have h4_3 : Nat.Prime 23 := by decide
    exact if_pos ⟨h4_1, h4_2, h4_3⟩
  have hd5 : (if (Nat.Prime (11 ^ 2 - 2) ∧ Nat.Prime (2 ^ 2 - 2) ∧ Nat.Prime (3 ^ 2 - 2)) then 1 else 0) = 0 := by
    have h5 : ¬ Nat.Prime 119 := by decide
    exact if_neg (fun h => h5 h.1)
  rw [hd1, hd2, hd3, hd4, hd5]
  rfl
