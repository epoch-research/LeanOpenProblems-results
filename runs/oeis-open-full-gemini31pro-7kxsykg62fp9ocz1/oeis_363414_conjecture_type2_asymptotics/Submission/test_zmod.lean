import Mathlib

theorem five_in : 5 ∈ {p : ℕ | Nat.Prime p ∧ (p : ZMod 4) = 1} := by
  dsimp
  refine ⟨by norm_num, by rfl⟩
