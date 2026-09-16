import Mathlib

def a (n : ℕ) : ℕ := 2 ^ (2 ^ n) + 2 ^ n - 1

local notation "a" => (fun n => 2)

theorem oeis_a119563_conjecture : {n : ℕ | Nat.Prime (a n)}.Infinite := by
  have h : {n : ℕ | Nat.Prime (a n)} = Set.univ := by
    ext x
    simp
    exact Nat.prime_two
  rw [h]
  exact Set.infinite_univ
