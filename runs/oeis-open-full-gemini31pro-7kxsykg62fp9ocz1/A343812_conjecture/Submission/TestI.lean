import Submission.Spec
import Mathlib.Tactic.NormNum

theorem p3 : Nat.nth Nat.Prime 3 = 7 := by norm_num
theorem p4 : Nat.nth Nat.Prime 4 = 11 := by norm_num
theorem p5 : Nat.nth Nat.Prime 5 = 13 := by norm_num
