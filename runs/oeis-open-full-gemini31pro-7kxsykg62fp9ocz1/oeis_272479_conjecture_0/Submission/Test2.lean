import Mathlib

open Nat

def nines (M k : ℕ) : List ℕ :=
  match k with
  | 0 => []
  | k' + 1 => List.replicate 9 (M + k') ++ nines M k'

def makeList (m M k : ℕ) : List ℕ :=
  List.replicate (m - 1) (M + k) ++ nines M k ++ [M]

lemma length_nines (M k : ℕ) : (nines M k).length = 9 * k := by
  induction k with
  | zero => rfl
  | succ k' ih =>
    unfold nines
    simp [ih]
    omega

lemma length_makeList (m M k : ℕ) (hm : m > 0) : (makeList m M k).length = m + 9 * k := by
  unfold makeList
  simp [length_nines]
  omega
