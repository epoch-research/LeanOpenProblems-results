import FormalConjectures.Util.ProblemImports
open Nat Set

def rep_threes (k : ℕ) : ℕ := (10 ^ k - 1) / 3
def num_digits (p : ℕ) : ℕ := (Nat.digits 10 p).length
def concatenate (k p : ℕ) : ℕ := rep_threes k * (10 ^ (num_digits p)) + p
noncomputable def prime_of_index (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)
noncomputable def A242775 (n : ℕ) : ℕ := if n = 0 then 0 else let P_n := prime_of_index n; let S : Set ℕ := { k : ℕ | k > 0 ∧ Nat.Prime (concatenate k P_n) }; sInf S
example : ∀ n, 4 ≤ n → A242775 n > 0 := by
  intro n hn
  simp [A242775]
