import Mathlib

partial def loop (n : Nat) : Nat :=
  if n == 0 then 0 else loop (n - 1) + 1

theorem test : loop 10 = 10 := by native_decide
