import Mathlib

open Nat

def M (n : ℕ) : ℕ := (Finset.range (n + 1)).sup (fun k => min (n.choose k) (2 ^ k))

lemma M_le_sup (n : ℕ) (k : ℕ) (hk : k ≤ n) : min (n.choose k) (2 ^ k) ≤ M n := by
  have : k ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk)
  exact @Finset.le_sup _ ℕ _ _ (Finset.range (n + 1)) (fun k => min (n.choose k) (2 ^ k)) k this
