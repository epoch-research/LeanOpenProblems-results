import Submission.Spec

example (a b : ℕ) (h : a ≤ b) : a.factorial ≤ b.factorial := by
  exact Nat.factorial_le_of_le h
