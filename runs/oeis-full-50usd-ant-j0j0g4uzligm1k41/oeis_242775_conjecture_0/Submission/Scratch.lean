import FormalConjectures.Util.ProblemImports

open Nat Set

def rep_threes (k : ℕ) : ℕ := (10 ^ k - 1) / 3
def num_digits (p : ℕ) : ℕ := (Nat.digits 10 p).length
def concatenate (k p : ℕ) : ℕ :=
  rep_threes k * (10 ^ (num_digits p)) + p
noncomputable def prime_of_index (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)
noncomputable def A242775 (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let P_n := prime_of_index n
    let S : Set ℕ := { k : ℕ | k > 0 ∧ Nat.Prime (concatenate k P_n) }
    sInf S

-- Warm-up: understand prime_of_index 4 = 7
example : prime_of_index 4 = 7 := by
  unfold prime_of_index
  norm_num


-- concatenate 1 7 = 37
example : concatenate 1 7 = 37 := by
  unfold concatenate rep_threes num_digits
  norm_num

-- Full theorem structure, reducing to the (open) core existence statement.
theorem test_conj : ∀ n, 4 ≤ n → A242775 n > 0 := by
  intro n hn
  have hn0 : n ≠ 0 := by omega
  have hcore : ∃ k, k > 0 ∧ Nat.Prime (concatenate k (prime_of_index n)) := by
    sorry
  simp only [A242775, hn0, if_false]
  obtain ⟨k, hk, hkp⟩ := hcore
  set S : Set ℕ := { k : ℕ | k > 0 ∧ Nat.Prime (concatenate k (prime_of_index n)) } with hS
  have hne : S.Nonempty := ⟨k, hk, hkp⟩
  exact (Nat.sInf_mem hne).1
