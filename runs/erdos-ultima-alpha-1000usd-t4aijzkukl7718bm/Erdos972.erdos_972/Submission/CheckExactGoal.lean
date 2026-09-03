import FormalConjecturesUtil
/-! Scratch theorem search for the unmodified prime-pair statement. -/
set_option maxHeartbeats 1000000 in
example : ∀ α : ℝ, α > 1 → Irrational α →
    ({p : ℕ | Nat.Prime p ∧ Nat.Prime ⌊α * p⌋₊} : Set ℕ).Infinite := by
  intro α hα hI
  exact?
