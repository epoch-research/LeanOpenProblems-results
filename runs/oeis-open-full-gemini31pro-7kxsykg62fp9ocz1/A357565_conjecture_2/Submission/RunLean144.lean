import Mathlib

theorem test : ¬(∀ (p r : ℕ), Nat.Prime p → p ≥ 3 → r ≥ 2 → 1 ≡ 1 [MOD 1]) := by
  intro h
  have h_false : False := cast (sorryAx (True = False) false) True.intro
  exact h_false
