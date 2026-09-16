import Submission.Spec

theorem a007406_conjecture_0_disproof : ¬ (∀ (n : ℕ), n > 3 → Nat.gcd n (Submission.Spec.a (n - 1)) = Submission.Spec.a089026 n) := by
  intro h
  have h4 := h 4 (by decide)
  revert h4
  decide
