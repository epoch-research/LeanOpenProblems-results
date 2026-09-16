import Submission.Spec
open Nat

theorem disproof : ¬ (∀ p, p.Prime → p ≥ 3 → A357674 p ≡ A357674 1 [MOD p ^ 5]) := by
  intro h
  have h3 := h 3 (by decide) (by decide)
  revert h3
  decide
