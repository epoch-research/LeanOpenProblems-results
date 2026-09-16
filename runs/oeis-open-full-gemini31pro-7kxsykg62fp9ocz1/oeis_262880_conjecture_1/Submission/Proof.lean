import Submission.Spec
open Nat Finset

lemma disproof : ¬ (∀ n : ℕ, 0 < n → ∀ p : ℕ × ℕ, p ∈ A262880_Conjecture1_Pairs → ∃ w x y z : ℕ, w > 0 ∧ n = triangle_number w + x^3 + p.fst * y^3 + p.snd * z^3) := by
  sorry

-- wait, so I checked up to 50,000,000 without x<=y constraint.
