import Submission.Spec
open Nat Finset

theorem proof1 : A329073_b 1 % 2 = 1 ↔ Nat.isPowerOfTwo 1 := by
  constructor
  · intro
    exact ⟨0, rfl⟩
  · intro
    rfl
