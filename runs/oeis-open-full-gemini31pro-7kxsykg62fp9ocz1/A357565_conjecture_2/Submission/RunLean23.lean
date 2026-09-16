import Submission.Spec
open Finset Nat

theorem disproof_thm : ¬ ∀ (p r : ℕ), Nat.Prime p → p ≥ 3 → r ≥ 2 →
    (A357565 (p ^ r)) ≡ (A357565 (p ^ (r - 1))) [MOD (p ^ (3 * r + 3))] := by
  intro h
  have h2 := h 79 2 (by decide) (by decide) (by decide)
  revert h2
  decide
