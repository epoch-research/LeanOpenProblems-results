import Submission.Spec

open Nat

example (m : ℕ) : A340737 (2*m + 3) = 2 * A340737 (2*m + 2) + (2*m + 3) * A340737 (2*m + 1) := by
  rw [A340737]
  simp only
  have hodd : (2 * m + 3) % 2 ≠ 0 := by omega
  simp [hodd]
  congr <;> omega

example (m : ℕ) : A340738 (2*m + 3) = 2 * A340738 (2*m + 2) + (2*m + 3) * A340738 (2*m + 1) := by
  rw [A340738]
  simp only
  have hodd : (2 * m + 3) % 2 ≠ 0 := by omega
  simp [hodd]
  congr <;> omega
