import Submission.Spec
import Mathlib.Tactic

theorem oeis_83753_conjecture_0_proof :
  ∀ (m k : ℕ),
    m > 1 ∧
    (Nat.digits 10 m = (Nat.digits 10 m).reverse) ∧
    k ≥ 5 ∧
    (∃ x : ℕ, m = x ^ k)
    →
    False
:= by
  intros m k h
  sorry
