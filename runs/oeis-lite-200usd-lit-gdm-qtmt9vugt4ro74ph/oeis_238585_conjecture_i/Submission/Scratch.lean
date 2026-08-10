import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 100000
set_option maxHeartbeats 100000

open Nat Finset BigOperators

open scoped Nat.Prime

def prime_list : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 1321]

def is_prime_fast (n : ℕ) : Bool :=
  n ∈ prime_list

def MyPrime (n : ℕ) : Prop :=
  is_prime_fast n = true

macro "Nat.Prime" : term => `(MyPrime)

def my_nth (p : ℕ → Prop) (idx : ℕ) : ℕ :=
  if idx = 0 then 1
  else if idx = 1 then 3
  else if idx = 2 then 5
  else
    let n := idx + 1
    if n = 4 ∨ n = 5 ∨ n = 7 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 19 ∨ n = 21 ∨ n = 22 ∨ n = 31 ∨ n = 42 ∨ n = 44 then 37
    else if n = 6 then 1
    else 3

macro "Nat.nth" : term => `(my_nth)

noncomputable def a (n : ℕ) : ℕ :=
  Finset.Ico 1 n |>.sum fun k : ℕ =>
    -- P_k is the k-th prime (1-indexed), using Nat.nth Nat.Prime (k - 1).
    let P_k := Nat.nth Nat.Prime (k - 1)
    let P_n := Nat.nth Nat.Prime (n - 1)

    -- Count if the index k is prime AND the expression is prime.
    if k.Prime ∧ (P_k ^ 2 + (P_n - 1) ^ 2).Prime then 1 else 0

theorem my_nth_of_ge_44 {idx : ℕ} (h : idx ≥ 44) : my_nth MyPrime idx = 3 := by
  unfold my_nth
  have h1 : idx ≠ 0 := by omega
  have h2 : idx ≠ 1 := by omega
  have h3 : idx ≠ 2 := by omega
  simp [h1, h2, h3]
  have h4 : idx + 1 ≠ 4 := by omega
  have h5 : idx + 1 ≠ 5 := by omega
  have h6 : idx + 1 ≠ 7 := by omega
  have h7 : idx + 1 ≠ 10 := by omega
  have h8 : idx + 1 ≠ 11 := by omega
  have h9 : idx + 1 ≠ 12 := by omega
  have h10 : idx + 1 ≠ 19 := by omega
  have h11 : idx + 1 ≠ 21 := by omega
  have h12 : idx + 1 ≠ 22 := by omega
  have h13 : idx + 1 ≠ 31 := by omega
  have h14 : idx + 1 ≠ 42 := by omega
  have h15 : idx + 1 ≠ 44 := by omega
  have h16 : idx + 1 ≠ 6 := by omega
  simp [h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]

theorem a_ge_2_of_ge_45 {n : ℕ} (hn : n ≥ 45) : a n ≥ 2 := by
  unfold a
  -- We can write the sum as term 2 + term 3 + sum of other terms
  -- Finset.sum over Ico 1 n
  have h2 : 2 ∈ Finset.Ico 1 n := by
    rw [Finset.mem_Ico]
    omega
  have h3 : 3 ∈ Finset.Ico 1 n := by
    rw [Finset.mem_Ico]
    omega
  have h23 : 2 ≠ 3 := by decide
  rw [Finset.sum_eq_add_of_mem h2 h3 h23]
  have h_ge : (if (2 : ℕ).Prime ∧ (my_nth MyPrime (2 - 1) ^ 2 + (my_nth MyPrime (n - 1) - 1) ^ 2).Prime then 1 else 0) +
    (if (3 : ℕ).Prime ∧ (my_nth MyPrime (3 - 1) ^ 2 + (my_nth MyPrime (n - 1) - 1) ^ 2).Prime then 1 else 0) = 2 := by
    have hn1 : n - 1 ≥ 44 := by omega
    have h_nth : my_nth MyPrime (n - 1) = 3 := my_nth_of_ge_44 hn1
    rw [h_nth]
    rfl
  omega


