import Mathlib

theorem test : ¬(∀ (p r : ℕ), Nat.Prime p → p ≥ 3 → r ≥ 2 → 1 ≡ 1 [MOD 1]) := by
  intro h
  have h2 : 1 ≡ 1 [MOD 1] := h 79 2 (by decide) (by decide) (by decide)
  sorry
