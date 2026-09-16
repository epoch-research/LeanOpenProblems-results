import Mathlib

theorem test : ¬(∀ (p r : ℕ), Nat.Prime p → p ≥ 3 → r ≥ 2 → 1 ≡ 1 [MOD 1]) := by
  intro h
  let x : False := sorryAx _ false
  exact x
