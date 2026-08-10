import Submission.Spec

open Nat Classical

example : reverse_nat 68899199886 = 68899199886 := by native_decide

example : 3^12 ∣ 68899199886 := by native_decide

example : ∀ k < 37, ¬ (k > 0 ∧ 27 ∣ reverse_nat (k * 27)) := by native_decide
