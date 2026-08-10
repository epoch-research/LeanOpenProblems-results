import FormalConjectures.Util.ProblemImports

open Nat Set

def rep_threes (k : ℕ) : ℕ := (10 ^ k - 1) / 3
def num_digits (p : ℕ) : ℕ := (Nat.digits 10 p).length
def concatenate (k p : ℕ) : ℕ := rep_threes k * (10 ^ (num_digits p)) + p
noncomputable def prime_of_index (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

-- check computables
#eval rep_threes 1   -- 3
#eval rep_threes 2   -- 33
#eval num_digits 7   -- 1
#eval concatenate 1 7 -- 37
#eval concatenate 2 19 -- 3319

noncomputable def A242775 (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let P_n := prime_of_index n
    let S : Set ℕ := { k : ℕ | k > 0 ∧ Nat.Prime (concatenate k P_n) }
    sInf S

example (n : ℕ) (hn : 4 ≤ n) : A242775 n > 0 := by
  unfold A242775
  rw [if_neg (show n ≠ 0 by omega)]
  have hne : {k | k > 0 ∧ Nat.Prime (concatenate k (prime_of_index n))}.Nonempty := by
    sorry
  have hmem := Nat.sInf_mem hne
  exact hmem.1
