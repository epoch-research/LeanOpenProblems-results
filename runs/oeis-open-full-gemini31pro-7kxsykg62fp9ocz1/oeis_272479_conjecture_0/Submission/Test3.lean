import Mathlib

open Nat

@[simp]
def nines (M k : ℕ) : List ℕ :=
  match k with
  | 0 => []
  | k' + 1 => List.replicate 9 (M + k') ++ nines M k'

def makeList (m M k : ℕ) : List ℕ :=
  List.replicate (m - 1) (M + k) ++ nines M k ++ [M]

lemma sum_nines (M k : ℕ) : ((nines M k).map (fun x => 10^x)).sum = 10^(M + k) - 10^M := by
  induction k with
  | zero => simp
  | succ k' ih =>
    unfold nines
    simp [ih]
    have h1 : 10^(M + (k' + 1)) = 10^(M + k') * 10 := by
      rw [← add_assoc, pow_succ]
    have h2 : 10^M ≤ 10^(M + k') := Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _)
    omega
