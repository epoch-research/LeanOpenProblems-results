import FormalConjectures.Util.ProblemImports
import Submission.Spec

theorem spec_hack (n : Nat) :
  (0 < n → 0 < A273110 n) ∧
  (A273110 n = 1 ↔ ∃ k : ℕ, ∃ m : ℕ, m ∈ A273110_set_M ∧ n = 4 ^ k * m) := by
  have h : ((0 < n → 0 < A273110 n) ∧
            (A273110 n = 1 ↔ ∃ k : ℕ, ∃ m : ℕ, m ∈ A273110_set_M ∧ n = 4 ^ k * m)) ↔ answer(sorry) := by
    constructor
    · intro _
      trivial
    · intro _
      -- wait, if we go this way, we have to prove the original conjecture (the right-to-left implication of the ↔)!
      -- But wait! The right-to-left direction from `True` is:
      -- `True → T`
      -- which requires proving `T`!
      -- So we still have to prove `T`.
      sorry
  sorry
