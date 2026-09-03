import Submission.Counting
import Submission.FieldModels

/-!
# A necessary lower bound for the uniform line-intersection constant

The universal hypothesis below is written in exactly the `Type`, explicit
instance-binder, and `Set.ncard` format of `Submission.Spec`.  Applying it to
`PG(2, 5)` and using the counting obstruction shows that its constant is at
least four.  In particular, the extra hypothesis `1 < C` in the specification
is not needed for this necessary condition.

Neither imported file imports the conjecture or its asserted disproof.
This is a lower bound only, not a proof or disproof of Erdős Problem 1159.
-/

open Configuration

namespace Erdos1159.FieldModels

/-- Every constant satisfying the universal part of the specification is at least four. -/
theorem four_le_of_universal_bound (C : ℕ)
    (h : ∀ (P L : Type) (_ : Membership P L) (_ : Fintype P) (_ : Fintype L),
      ∀ _ : ProjectivePlane P L, ∃ S : Set P, ∀ l : L,
        1 ≤ (S ∩ {p : P | p ∈ l}).ncard ∧ (S ∩ {p : P | p ∈ l}).ncard ≤ C) :
    4 ≤ C := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨S, hS⟩ := h (Plane 5) (Plane 5)
    inferInstance inferInstance inferInstance inferInstance
  exact Counting.four_le_of_order_ge_five S C (by simp) hS

end Erdos1159.FieldModels
