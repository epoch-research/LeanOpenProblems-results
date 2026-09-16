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

lemma sum_makeList (m M k : ℕ) (hm : m > 0) :
  ((makeList m M k).map (fun x => 10^x)).sum = m * 10^(M + k) := by
  unfold makeList
  simp [sum_nines]
  have h2 : 10^M ≤ 10^(M + k) := Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _)
  have h3 : (m - 1) * 10^(M + k) = m * 10^(M + k) - 10^(M + k) := by
    rw [tsub_mul, one_mul]
  have h4 : 10^(M + k) ≤ m * 10^(M + k) := by
    calc 10^(M + k) = 1 * 10^(M + k) := (one_mul _).symm
      _ ≤ m * 10^(M + k) := Nat.mul_le_mul_right _ hm
  omega
