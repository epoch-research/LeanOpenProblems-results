import Submission.Spec
open Mathlib

theorem test {p : ℕ} (h : IsInA003625 p) : a (p * (p - 1)) ≡ p ^ 2 [MOD p ^ 3] := by
  aesop
