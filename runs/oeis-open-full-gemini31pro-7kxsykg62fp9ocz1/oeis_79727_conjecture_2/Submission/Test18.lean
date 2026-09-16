import Submission.Spec
open Mathlib

theorem test : IsInA003625 7 := by
  unfold IsInA003625
  have h1 : Nat.Prime 7 := by norm_num
  have h2 : 7 % 14 = 7 := by rfl
  aesop
