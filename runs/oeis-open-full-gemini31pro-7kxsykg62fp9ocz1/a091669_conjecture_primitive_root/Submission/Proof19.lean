import Mathlib

open Nat BigOperators

lemma prod_pos (n : ℕ) : (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) > 0 := by
  apply Finset.prod_pos
  intro k hk
  rw [Finset.mem_Ico] at hk
  have h1 : 2 ^ k > 1 := by
    calc 2 ^ k ≥ 2 ^ 1 := Nat.pow_le_pow_right (by decide) hk.1
      _ = 2 := by decide
      _ > 1 := by decide
  omega
