import Mathlib

def sieveAndCheck (limit : ℕ) (n : ℕ) : Bool :=
  let rec loop (i : ℕ) (sum : ℕ) : ℕ :=
    if h : i = 0 then sum else loop (i - 1) (sum + 1)
  termination_by i
  decreasing_by omega
  loop limit 0 == limit

theorem test_sieve : sieveAndCheck 10000000 10 = true := by native_decide
