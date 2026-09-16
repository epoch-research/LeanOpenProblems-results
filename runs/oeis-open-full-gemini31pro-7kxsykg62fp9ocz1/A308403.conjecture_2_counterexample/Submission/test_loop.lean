import Mathlib

def simpleLoop (n : ℕ) : ℕ :=
  let rec loop (i : ℕ) (sum : ℕ) : ℕ :=
    if i == 0 then sum else loop (i - 1) (sum + 1)
  termination_by i
  loop n 0

theorem test_loop : simpleLoop 1000000000 = 1000000000 := by native_decide
