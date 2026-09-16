import Mathlib

def loop416m (n : ℕ) : ℕ :=
  let rec loop (i : ℕ) (sum : ℕ) : ℕ :=
    if h : i = 0 then sum else loop (i - 1) (sum + 1)
  termination_by i
  decreasing_by omega
  loop n 0

theorem test_loop : loop416m 416000000 = 416000000 := by native_decide
