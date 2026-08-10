import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

example (k : Nat) (h_cass_fib_z : (Nat.fib (k + 1) : ℤ)^2 = (Nat.fib (k + 2) : ℤ) * (Nat.fib k : ℤ) + 1) :
  (Nat.fib (k + 1) : ℤ)^2 - (Nat.fib k : ℤ) * (Nat.fib (k + 2) : ℤ) + 1 = 0 := by
  linear_combination h_cass_fib_z
