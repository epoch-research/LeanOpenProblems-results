import Submission.Reduction
import Submission.Weighted

/-! The exact remaining sufficient strategy bound for the disproof. This file does not
assume either theorem in Spec.lean and does not assert the missing strategy bound. -/

open Combinatorics Real Filter WeightedVertexOnline

/-- A cofinal family of sufficiently small weighted strategies would refute the statement.
The hypothesis is the outstanding combinatorial problem, not an established estimate. -/
theorem disproof_of_small_weighted_strategies
    (h : ∀ N : ℕ, ∃ k ≥ N, ∃ T : MoveTree,
      Forces k T ∧ T.J + 1 < (2 : ℕ) ^ (2 ^ (k + 1))) :
    ¬ (∃ c > 0, ∀ᶠ n in atTop,
      (2 : ℝ) ^ (2 : ℝ) ^ (c * n) ≤ hypergraphRamsey 3 n) := by
  apply exact_negation.mpr
  intro N
  obtain ⟨k, hk, T, hT, hbudget⟩ := h N
  exact ⟨k + 1, by omega, lt_of_le_of_lt (weighted_transfer hT) hbudget⟩

#print axioms disproof_of_small_weighted_strategies
